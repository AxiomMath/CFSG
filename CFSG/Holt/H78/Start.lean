module

public import CFSG.Holt.H78.SectionsStar
public import CFSG.Holt.H78.DataTransport
public import CFSG.Holt.H78.DataSylow
import CFSG.Holt.H78.JImages
import CFSG.Holt.H78.DataSocle
import CFSG.Holt.H78.AltModelAut
import CFSG.Holt.H78.SEModelFive
import CFSG.Holt.H78.DataPrimitive

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General
open scoped Pointwise

section Generic

variable {X : Type*} [Group X]

theorem inf_eq_bot_or_le_of_isSimpleGroup {L V : Subgroup X} [IsSimpleGroup L]
    (hV : ∀ l ∈ L, ∀ v ∈ V, l * v * l⁻¹ ∈ V) : V ⊓ L = ⊥ ∨ L ≤ V := by
  have hn : (V.subgroupOf L).Normal := ⟨fun v hv l => by
    rw [Subgroup.mem_subgroupOf] at hv ⊢
    simpa using hV l l.2 v hv⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (V.subgroupOf L) with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hx.2⟩ : L) ∈ V.subgroupOf L := hx.1
    rw [h, Subgroup.mem_bot] at hx'
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hx')
  · exact Or.inr (Subgroup.subgroupOf_eq_top.mp h)

theorem commute_of_inf_eq_bot {A B : Subgroup X} (hA : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A)
    (hB : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ ∈ B) (h : A ⊓ B = ⊥) {a b : X} (ha : a ∈ A)
    (hb : b ∈ B) : a * b = b * a := by
  have hc : a * b * a⁻¹ * b⁻¹ ∈ A ⊓ B := by
    refine ⟨?_, B.mul_mem (hB a ha b hb) (B.inv_mem hb)⟩
    have : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
    rw [this]
    exact A.mul_mem ha (hA b hb _ (A.inv_mem ha))
  rw [h, Subgroup.mem_bot] at hc
  calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
    _ = b * a := by rw [hc, one_mul]

theorem le_of_forall_commute_eq_one {N M L V : Subgroup X} [IsSimpleGroup L]
    (hperf : ⁅L, L⁆ = L) (hLM : L ≤ M) (hMN : M ≤ N) (hVN : V ≤ N)
    (hM : ∀ n ∈ N, ∀ m ∈ M, n * m * n⁻¹ ∈ M) (hL : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L)
    (hV : ∀ n ∈ N, ∀ v ∈ V, n * v * n⁻¹ ∈ V)
    (hC : ∀ n ∈ N, (∀ v ∈ V, n * v = v * n) → n = 1) : L ≤ V := by
  rcases inf_eq_bot_or_le_of_isSimpleGroup (fun l hl v hv => hV l (hMN (hLM hl)) v hv) with
    h | h
  · exfalso
    have h1 : ⁅V, L⁆ ≤ V ⊓ M := by
      rw [Subgroup.commutator_le]
      intro v hv l hl
      rw [commutatorElement_def]
      refine ⟨?_, M.mul_mem (hM v (hVN hv) l (hLM hl)) (M.inv_mem (hLM hl))⟩
      have : v * l * v⁻¹ * l⁻¹ = v * (l * v⁻¹ * l⁻¹) := by group
      rw [this]
      exact V.mul_mem hv (hV l (hMN (hLM hl)) _ (V.inv_mem hv))
    have h2 : ⁅V ⊓ M, L⁆ = ⊥ := by
      rw [eq_bot_iff, ← h, Subgroup.commutator_le]
      intro c hc l hl
      rw [commutatorElement_def]
      refine ⟨?_, L.mul_mem (hL c hc.2 l hl) (L.inv_mem hl)⟩
      have : c * l * c⁻¹ * l⁻¹ = c * (l * c⁻¹ * l⁻¹) := by group
      rw [this]
      exact V.mul_mem hc.1 (hV l (hMN (hLM hl)) _ (V.inv_mem hc.1))
    have h3 : ⁅⁅V, L⁆, L⁆ = ⊥ :=
      le_bot_iff.mp ((Subgroup.commutator_mono h1 le_rfl).trans h2.le)
    have h4 : ⁅⁅L, V⁆, L⁆ = ⊥ := by rwa [Subgroup.commutator_comm L V]
    have h5 : ⁅⁅L, L⁆, V⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h4 h3
    rw [hperf] at h5
    have hL1 : ∀ l ∈ L, l = 1 := fun l hl => hC l (hMN (hLM hl)) fun v hv => by
      have hlv := Subgroup.commutator_mem_commutator hl hv
      rw [h5, Subgroup.mem_bot, commutatorElement_def] at hlv
      calc l * v = l * v * l⁻¹ * v⁻¹ * (v * l) := by group
        _ = v * l := by rw [hlv, one_mul]
    obtain ⟨x, hx⟩ := exists_ne (1 : L)
    exact hx (Subtype.ext (hL1 x x.2))
  · exact h

theorem commutator_le_of_relIndex_le_two [Finite X] {A B : Subgroup X}
    (h2 : A.relIndex B ≤ 2) : ⁅B, B⁆ ≤ A := by
  have h0 : A.relIndex B ≠ 0 :=
    (Subgroup.index_ne_zero_of_finite : (A.subgroupOf B).index ≠ 0)
  rcases (by omega : A.relIndex B = 1 ∨ A.relIndex B = 2) with h1 | h2'
  · refine Subgroup.commutator_le.mpr fun x hx y hy => Subgroup.relIndex_eq_one.mp h1 ?_
    rw [commutatorElement_def]
    exact B.mul_mem (B.mul_mem (B.mul_mem hx hy) (B.inv_mem hx)) (B.inv_mem hy)
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hidx : (A.subgroupOf B).index = 2 := h2'
  have key : ∀ a b : B, a * b ∈ A.subgroupOf B ↔ (a ∈ A.subgroupOf B ↔ b ∈ A.subgroupOf B) :=
    fun a b => Subgroup.mul_mem_iff_of_index_two hidx
  have hmem : (⟨x, hx⟩ * ⟨y, hy⟩ : B) * ((⟨x, hx⟩ : B)⁻¹ * (⟨y, hy⟩ : B)⁻¹) ∈
      A.subgroupOf B := by
    rw [key, key, key, (A.subgroupOf B).inv_mem_iff, (A.subgroupOf B).inv_mem_iff]
  rw [Subgroup.mem_subgroupOf] at hmem
  simpa [commutatorElement_def, mul_assoc] using hmem

theorem relIndex_le_two_of_sup_zpowers [Finite X] {P B : Subgroup X} {τ : X}
    (hτ : τ * τ = 1) (hPB : P ≤ B) (hτB : τ ∈ B) (hnorm : ∀ b ∈ B, ∀ p ∈ P, b * p * b⁻¹ ∈ P)
    (hsup : Subgroup.zpowers τ ⊔ P = B) : P.relIndex B ≤ 2 := by
  have hn : (P.subgroupOf B).Normal := ⟨fun p hp b => by
    rw [Subgroup.mem_subgroupOf] at hp ⊢
    simpa using hnorm b b.2 p hp⟩
  have htop : Subgroup.zpowers (⟨τ, hτB⟩ : B) ⊔ P.subgroupOf B = ⊤ := by
    apply Subgroup.map_injective B.subtype_injective
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hPB, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hsup
  change (P.subgroupOf B).index ≤ 2
  rw [← Subgroup.relIndex_top_right, ← htop, Subgroup.relIndex_sup_right]
  calc (P.subgroupOf B).relIndex (Subgroup.zpowers (⟨τ, hτB⟩ : B))
      ≤ Nat.card (Subgroup.zpowers (⟨τ, hτB⟩ : B)) :=
        Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)
    _ = orderOf (⟨τ, hτB⟩ : B) := Nat.card_zpowers _
    _ ≤ 2 := Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one (by
        rw [pow_two]; exact Subtype.ext hτ))

theorem mem_normalizer_iSup {ι : Sort*} {U : ι → Subgroup X} {g : X}
    (h : ∀ i, g ∈ Subgroup.normalizer (U i : Set X)) :
    g ∈ Subgroup.normalizer ((⨆ i, U i : Subgroup X) : Set X) := by
  have key : ∀ g' : X, (∀ i, g' ∈ Subgroup.normalizer (U i : Set X)) →
      ∀ x ∈ ⨆ i, U i, g' * x * g'⁻¹ ∈ ⨆ i, U i := by
    intro g' hg' x hx
    have hle : (⨆ i, U i) ≤ (⨆ i, U i).comap (MulAut.conj g').toMonoidHom :=
      iSup_le fun i y hy => Subgroup.mem_iSup_of_mem i
        (((Subgroup.mem_normalizer_iff).mp (hg' i) y).mp hy)
    exact hle hx
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g h x, fun hx => ?_⟩
  have := key g⁻¹ (fun i => Subgroup.inv_mem _ (h i)) _ hx
  simpa [mul_assoc] using this

theorem isPGroup_iSup_of_commute {p : ℕ} {ι : Type*} [Finite ι] {U : ι → Subgroup X}
    (hU : ∀ i, IsPGroup p (U i))
    (hc : ∀ i j, i ≠ j → ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x) :
    IsPGroup p (⨆ i, U i : Subgroup X) := by
  have := Fintype.ofFinite ι
  classical
  suffices key : ∀ s : Finset ι, IsPGroup p (s.sup U : Subgroup X) by
    have h := key Finset.univ
    rwa [Finset.sup_univ_eq_iSup] at h
  intro s
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sup_empty]
    exact IsPGroup.of_bot
  | insert a s ha ih =>
    rw [Finset.sup_insert]
    refine (hU a).to_sup_of_normal_left' ih ?_
    refine Finset.sup_le fun j hj => ?_
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (hc j a (by rintro rfl; exact ha hj) y hy z hz).symm

theorem map_eq_bot_or_injective_of_isSimpleGroup {Z : Type*} [Group Z] {W : Subgroup X}
    [IsSimpleGroup W] (f : X →* Z) : W.map f = ⊥ ∨ Function.Injective (f.comp W.subtype) := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (f.comp W.subtype).ker with h | h
  · exact Or.inr ((MonoidHom.ker_eq_bot_iff _).mp h)
  · left
    rw [eq_bot_iff]
    rintro _ ⟨w, hw, rfl⟩
    have : (⟨w, hw⟩ : W) ∈ (f.comp W.subtype).ker := h ▸ Subgroup.mem_top _
    exact (Subgroup.mem_bot).mpr this

end Generic

section OddCore

variable {G : Type*} [Group G] [Finite G]

theorem pPrimeCore_eq_bot_of_normal {N : Subgroup G} [N.Normal]
    (hO : CFSG.pPrimeCore 2 G = ⊥) : CFSG.pPrimeCore 2 N = ⊥ := by
  have hn : ((CFSG.pPrimeCore 2 N).map N.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  have hle : (CFSG.pPrimeCore 2 N).map N.subtype ≤ CFSG.pPrimeCore 2 G :=
    le_sSup ⟨hn, by
      rw [Subgroup.card_map_of_injective N.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card⟩
  rwa [hO, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective] at hle

omit [Finite G] in
theorem eq_bot_of_odd_of_normal (hO : CFSG.pPrimeCore 2 G = ⊥) {Y : Subgroup G} [Y.Normal]
    (hY : Odd (Nat.card Y)) : Y = ⊥ :=
  (CFSG.pPrimeCore_eq_bot_iff.mp hO) Y inferInstance (Nat.coprime_two_left.mpr hY)

end OddCore

section BlockKernel

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

variable (G) in
@[expose] noncomputable def blockKernelHom (α : Ω) (K : Subgroup G) :
    K.normalCore →* (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).range :=
  (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).rangeRestrict.comp
    (Subgroup.inclusion K.normalCore_le)

@[simp] theorem blockKernelHom_smul {α : Ω} {K : Subgroup G} (n : K.normalCore)
    (c : K ⧸ (stabilizer G α).subgroupOf K) :
    blockKernelHom G α K n • c = (⟨n, K.normalCore_le n.2⟩ : K) • c := rfl

@[simp] theorem rangeRestrict_block_smul {α : Ω} {K : Subgroup G} (k : K)
    (c : K ⧸ (stabilizer G α).subgroupOf K) :
    (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).rangeRestrict k • c = k • c := rfl

variable [Finite G] [Finite Ω] [FaithfulSMul G Ω]

theorem blockKernelHom_injective (hG : IsStarGroup G Ω) {α : Ω} {K : Subgroup G}
    (hK : stabilizer G α ≤ K) (hO : CFSG.pPrimeCore 2 G = ⊥) :
    Function.Injective (blockKernelHom G α K) := by
  rw [injective_iff_map_eq_one]
  intro n hn
  have hfix : (n : G) ∈ fixingSubgroup G (orbit K α) := by
    rw [mem_fixingSubgroup_iff]
    intro ω hω
    obtain ⟨c, rfl⟩ := exists_blockPoint_eq hω
    have hc : (⟨n, K.normalCore_le n.2⟩ : K) • c = c := by
      rw [← blockKernelHom_smul, hn, one_smul]
    have := blockPoint_smul (α := α) (⟨n, K.normalCore_le n.2⟩ : K) c
    rw [hc] at this
    exact this.symm
  have hmem : (n : G) ∈ CFSG.pPrimeCore 2 G :=
    fixingSubgroup_inf_kernel_le_pPrimeCore hG hK ⟨hfix, n.2⟩
  rw [hO, Subgroup.mem_bot] at hmem
  exact Subtype.ext hmem

omit [Finite G] [Finite Ω] [FaithfulSMul G Ω] in
theorem isPreprimitive_range_block [Finite G] {α : Ω} {K : Subgroup G}
    (hαK : stabilizer G α < K)
    (hmin : ∀ K' : Subgroup G, stabilizer G α < K' → K' ≤ K → K' = K) :
    IsPreprimitive (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).range
      (K ⧸ (stabilizer G α).subgroupOf K) := by
  have hcoat : IsCoatom (stabilizer K ((1 : K) : K ⧸ (stabilizer G α).subgroupOf K)) := by
    rw [MulAction.stabilizer_quotient]
    refine ⟨fun h => hαK.not_ge (Subgroup.subgroupOf_eq_top.mp h), fun H hH => ?_⟩
    have hmap : ((stabilizer G α).subgroupOf K).map K.subtype = stabilizer G α := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hαK.le]
    have h1 : stabilizer G α < H.map K.subtype := by
      rw [← hmap]
      exact (Subgroup.map_lt_map_iff_of_injective K.subtype_injective).mpr hH
    have h2 := hmin _ h1 (Subgroup.map_subtype_le H)
    rw [eq_top_iff]
    intro k _
    have hk : (k : G) ∈ H.map K.subtype := by rw [h2]; exact k.2
    obtain ⟨h, hh, hhk⟩ := hk
    exact (Subtype.ext hhk : h = k) ▸ hh
  have hnt : Nontrivial (K ⧸ (stabilizer G α).subgroupOf K) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    have : (stabilizer G α).relIndex K ≠ 1 := fun h =>
      hαK.not_ge (Subgroup.relIndex_eq_one.mp h)
    have h0 : (stabilizer G α).relIndex K ≠ 0 :=
      (Subgroup.index_ne_zero_of_finite : ((stabilizer G α).subgroupOf K).index ≠ 0)
    change 1 < (stabilizer G α).relIndex K
    omega
  have : IsPreprimitive K (K ⧸ (stabilizer G α).subgroupOf K) :=
    (isCoatom_stabilizer_iff_preprimitive K _).mp hcoat
  let f : (K ⧸ (stabilizer G α).subgroupOf K) →ₑ[
      (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).rangeRestrict]
      (K ⧸ (stabilizer G α).subgroupOf K) :=
    { toFun := id
      map_smul' := fun _ _ => rfl }
  exact IsPreprimitive.of_surjective (f := f) Function.surjective_id

end BlockKernel

section TheoremOneBelow

variable {G : Type} [Group G] [Finite G] {Ω : Type} [MulAction G Ω] [Finite Ω]
  [FaithfulSMul G Ω]

omit [Finite Ω] [FaithfulSMul G Ω] in
theorem three_le_relIndex (hG : IsStarGroup G Ω) {α : Ω} {K : Subgroup G}
    (hαK : stabilizer G α < K) : 3 ≤ (stabilizer G α).relIndex K := by
  have := hG.isPretransitive
  obtain ⟨k, hk⟩ := odd_relIndex_of_le hG.odd_card hαK.le
  have : (stabilizer G α).relIndex K ≠ 1 := fun h => hαK.not_ge (Subgroup.relIndex_eq_one.mp h)
  omega

omit [Finite Ω] [FaithfulSMul G Ω] in
theorem three_le_index (hG : IsStarGroup G Ω) {α : Ω} {K : Subgroup G}
    (hαK : stabilizer G α ≤ K) (hK : K ≠ ⊤) : 3 ≤ K.index := by
  have := hG.isPretransitive
  obtain ⟨k, hk⟩ := odd_index_of_le hG.odd_card hαK
  have : K.index ≠ 1 := fun h => hK (Subgroup.index_eq_one.mp h)
  omega

omit [Finite Ω] [FaithfulSMul G Ω] in
theorem holtTheorem1Below_range_block (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω))
    (α : Ω) {K : Subgroup G} (hK : K ≠ ⊤) :
    HoltTheorem1Below (Nat.card (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).range)
      (Nat.card (K ⧸ (stabilizer G α).subgroupOf K) + 1) :=
  hB.mono (Or.inl (card_range_block_lt (lt_top_iff_ne_top.mpr hK)))

omit [FaithfulSMul G Ω] in
theorem holtStructure_range_block (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω)) {α : Ω} {K : Subgroup G}
    (hαK : stabilizer G α < K) (hK : K ≠ ⊤) :
    HoltStructure (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).range
      (K ⧸ (stabilizer G α).subgroupOf K) :=
  hB _ _ (Or.inl (card_range_block_lt (lt_top_iff_ne_top.mpr hK)))
    (isStarGroup_range_block hG hαK.le (three_le_relIndex hG hαK))

omit [FaithfulSMul G Ω] in
theorem holtTheorem1Below_range_quotient (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω)) {α : Ω} {K : Subgroup G}
    (hαK : stabilizer G α < K) :
    HoltTheorem1Below (Nat.card (toPermHom G (G ⧸ K)).range) (Nat.card (G ⧸ K) + 1) := by
  have := hG.isPretransitive
  exact hB.of_le (card_range_toPermHom_le _) (card_quotient_lt_card hαK)

omit [FaithfulSMul G Ω] in
theorem holtStructure_range_quotient (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω)) {α : Ω} {K : Subgroup G}
    (hαK : stabilizer G α < K) (hK : K ≠ ⊤) :
    HoltStructure (toPermHom G (G ⧸ K)).range (G ⧸ K) := by
  have := hG.isPretransitive
  exact hB _ _ (lex_lt_range_quotient hαK)
    (isStarGroup_range_quotient hG hαK.le (three_le_index hG hαK.le hK))

theorem holtStructure_of_jHull_ne_top (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω)) (hH : jHull G Ω ≠ ⊤) :
    HoltStructure G Ω := by
  rw [holtStructure_iff_jHull]
  have hlt := Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hH)
  rw [Subgroup.card_top] at hlt
  exact hB _ _ (Or.inl hlt) (isStarGroup_jHull hG)

end TheoremOneBelow

section TransitiveOddCore

variable {G : Type} [Group G] [Finite G] {Ω : Type} [MulAction G Ω] [Finite Ω]
  [FaithfulSMul G Ω]

omit [Finite G] [Finite Ω] [FaithfulSMul G Ω] in
theorem blockKernelHom_range_normal (α : Ω) (K : Subgroup G) :
    (blockKernelHom G α K).range.Normal := by
  refine ⟨fun y hy g => ?_⟩
  obtain ⟨n, rfl⟩ := hy
  obtain ⟨k, hk⟩ := g.2
  have hg : (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).rangeRestrict k = g :=
    Subtype.ext hk
  refine ⟨⟨(k : G) * n * (k : G)⁻¹, K.normalCore_normal.conj_mem n n.2 k⟩, ?_⟩
  have hincl : Subgroup.inclusion K.normalCore_le
      ⟨(k : G) * n * (k : G)⁻¹, K.normalCore_normal.conj_mem n n.2 k⟩ =
        k * Subgroup.inclusion K.normalCore_le n * k⁻¹ := Subtype.ext rfl
  rw [← hg]
  simp only [blockKernelHom, MonoidHom.coe_comp, Function.comp_apply, hincl, map_mul, map_inv]

theorem false_of_isPretransitive_oddCore_block (hG : IsStarGroup G Ω)
    (hO : CFSG.pPrimeCore 2 G = ⊥) {α : Ω} {K : Subgroup G} (hK : stabilizer G α ≤ K)
    (hN : K.normalCore ≠ ⊥)
    (hT : IsPretransitive (jOddCore (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).range
      (K ⧸ (stabilizer G α).subgroupOf K)) (K ⧸ (stabilizer G α).subgroupOf K)) : False := by
  have hκ : Function.Injective (blockKernelHom G α K) := blockKernelHom_injective hG hK hO
  have hκN := blockKernelHom_range_normal α K
  set O' := jOddCore (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).range
    (K ⧸ (stabilizer G α).subgroupOf K) with hO'
  have hY : O'.comap (blockKernelHom G α K) = ⊥ := by
    have hodd : Odd (Nat.card (O'.comap (blockKernelHom G α K))) := by
      rw [← Subgroup.card_map_of_injective hκ]
      exact Odd.of_dvd_nat odd_card_jOddCore
        (Subgroup.card_dvd_of_le (Subgroup.map_comap_le _ _))
    exact eq_bot_of_odd_of_normal (pPrimeCore_eq_bot_of_normal hO) hodd
  have hinf : (blockKernelHom G α K).range ⊓ O' = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨⟨n, rfl⟩, hn⟩
    have hn' : n ∈ O'.comap (blockKernelHom G α K) := hn
    rw [hY, Subgroup.mem_bot] at hn'
    rw [hn', map_one]
    exact Subgroup.one_mem _
  have hcomm : ∀ n : K.normalCore, ∀ o ∈ O',
      blockKernelHom G α K n * o = o * blockKernelHom G α K n := fun n o ho =>
    commute_of_inf_eq_bot (fun b _ a ha => hκN.conj_mem a ha b)
      (fun a _ b hb => (jOddCore_normal).conj_mem b hb a) hinf ⟨n, rfl⟩ ho
  have hodd : Odd (Nat.card (K ⧸ (stabilizer G α).subgroupOf K)) := by
    have := hG.isPretransitive
    exact odd_relIndex_of_le hG.odd_card hK
  have hinv : ∀ n : K.normalCore, orderOf n ≠ 2 := by
    intro n hn2
    have hy2 : orderOf (blockKernelHom G α K n) = 2 := by
      rw [orderOf_injective _ hκ n, hn2]
    have hP : IsPGroup 2 (Subgroup.zpowers (blockKernelHom G α K n)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy2, pow_one])
    obtain ⟨b, hb⟩ := fixSet_nonempty_of_odd hodd hP
    have hfix : ∀ c : K ⧸ (stabilizer G α).subgroupOf K, blockKernelHom G α K n • c = c := by
      intro c
      obtain ⟨o, rfl⟩ := exists_smul_eq O' b c
      change blockKernelHom G α K n •
          ((o : (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).range) • b) =
        (o : (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).range) • b
      rw [← mul_smul, hcomm n o o.2, mul_smul, hb _ (Subgroup.mem_zpowers _)]
    have h1 : blockKernelHom G α K n = 1 := Subtype.ext (Equiv.ext hfix)
    rw [h1, orderOf_one] at hy2
    exact absurd hy2 (by norm_num)
  have hNodd : Odd (Nat.card K.normalCore) := by
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    intro h2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := exists_prime_orderOf_dvd_card' 2 h2
    exact hinv n hn
  exact hN (eq_bot_of_odd_of_normal hO hNodd)

end TransitiveOddCore

section WFacts

variable {X : Type*} [Group X] [Finite X] {Δ : Type*} [MulAction X Δ]

theorem HoltData.even_card_W (D : HoltData X Δ) (hO : jOddCore X Δ = ⊥) (B : Δ) {i : D.ι}
    (hM : D.M i = alternatingGroup (D.Ψc i)) (h7 : 7 ≤ Fintype.card (D.Ψc i)) :
    Even (Nat.card (D.W B i)) := by
  rw [Nat.card_congr (D.wEquiv hO B i).toEquiv, D.wModel_eq_of_alternatingGroup B hM h7]
  have h2 := two_mul_card_alternatingGroup_inf_stabilizer
    (by omega : 3 ≤ Fintype.card (D.Ψc i)) (D.coord B i)
  obtain ⟨m, hm⟩ : 4 ∣ (Fintype.card (D.Ψc i) - 1).factorial :=
    Nat.dvd_factorial (by norm_num) (by omega)
  exact ⟨m, by omega⟩

omit [Finite X] in
theorem isPGroup_two_of_mul_self_eq_one {W : Subgroup X} (hW : ∀ w ∈ W, w * w = 1) :
    IsPGroup 2 W := fun w => ⟨1, by rw [pow_one, pow_two]; exact Subtype.ext (hW w w.2)⟩

end WFacts

section KernelTrivial

variable {G : Type} [Group G] [Finite G] {Ω : Type} [MulAction G Ω] [Finite Ω]
  [FaithfulSMul G Ω]

omit [Finite G] [Finite Ω] [FaithfulSMul G Ω] in
theorem mem_longInvAt_quotient [IsPretransitive G Ω] (hΩ : Odd (Nat.card Ω)) {α : Ω}
    {K : Subgroup G} (hK : stabilizer G α ≤ K) {t : G} {β : Ω} (ht : t ∈ longInvAt G Ω β) :
    t ∈ longInvAt G (G ⧸ K) (blockCoset α K β) := by
  have hfix := (smul_eq_iff_of_mem_longInvAt_quotient hΩ hK ht (blockCoset α K β)).mpr rfl
  exact ⟨⟨ht.1.1, blockCoset α K β, hfix, fun c hc =>
    (smul_eq_iff_of_mem_longInvAt_quotient hΩ hK ht c).mp hc⟩, hfix⟩

omit [Finite G] [Finite Ω] [FaithfulSMul G Ω] in
theorem faithfulSMul_quotient_of_normalCore_eq_bot {K : Subgroup G}
    (hN : K.normalCore = ⊥) : FaithfulSMul G (G ⧸ K) := ⟨fun {g₁ g₂} h => by
  have hk : g₂⁻¹ * g₁ ∈ K.normalCore := by
    rw [Subgroup.normalCore_eq_ker, MonoidHom.mem_ker]
    ext c
    change (g₂⁻¹ * g₁) • c = c
    rw [mul_smul, h, inv_smul_smul]
  rw [hN, Subgroup.mem_bot, inv_mul_eq_one] at hk
  exact hk.symm⟩

omit [FaithfulSMul G Ω] in
theorem mem_longInvAt_one_quotient_iff (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω)) {α : Ω} {K : Subgroup G}
    (hαK : stabilizer G α < K) (hK : K ≠ ⊤) (hN : K.normalCore = ⊥) {u : G} :
    u ∈ longInvAt G (G ⧸ K) ((1 : G) : G ⧸ K) ↔ u ∈ longInv G Ω ∧ u ∈ K := by
  have := hG.isPretransitive
  have hinj : Function.Injective (toPermHom G (G ⧸ K)) := by
    rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.normalCore_eq_ker, hN]
  have hmemK : ∀ g : G, g • ((1 : G) : G ⧸ K) = ((1 : G) : G ⧸ K) ↔ g ∈ K := fun g => by
    rw [← mem_stabilizer_iff, MulAction.stabilizer_quotient]
  constructor
  · intro hu
    have hy : (toPermHom G (G ⧸ K)).rangeRestrict u ∈
        longInv (toPermHom G (G ⧸ K)).range (G ⧸ K) :=
      (mem_longInv_map_iff (e := Equiv.refl (G ⧸ K))
        (MonoidHom.rangeRestrict_injective_iff.mpr hinj) (fun _ _ => rfl) u).mpr hu.1
    obtain ⟨t, ht, htu⟩ := (mem_longInv_range_quotient_iff hG hαK.le
      (three_le_index hG hαK.le hK) (holtTheorem1Below_range_quotient hG hB hαK) _).mp hy
    rw [hinj htu] at ht
    exact ⟨ht, (hmemK u).mp hu.2⟩
  · rintro ⟨hu, huK⟩
    obtain ⟨β, hβ, -⟩ := hu.2
    have hu' := mem_longInvAt_quotient hG.odd_card hαK.le (t := u) (β := β) ⟨hu, hβ⟩
    have hfix := (hmemK u).mpr huK
    obtain ⟨c, -, hc⟩ := hu'.1.2
    have h1 := hc _ hfix
    have h2 := hc _ hu'.2
    exact ⟨hu'.1, h1 ▸ h2 ▸ hu'.2⟩

omit [FaithfulSMul G Ω] in
theorem jHull_range_block_eq (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω)) (hO : CFSG.pPrimeCore 2 G = ⊥)
    {α : Ω} {K : Subgroup G} (hαK : stabilizer G α < K) (hK : K ≠ ⊤) (hN : K.normalCore = ⊥)
    (D' : HoltData G (G ⧸ K)) {t : G} (ht : t ∈ longInvAt G Ω α) :
    jHull (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).range
        (K ⧸ (stabilizer G α).subgroupOf K) =
      Subgroup.zpowers ((toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).rangeRestrict
          ⟨t, hαK.le ht.2⟩) ⊔
        ⨆ i, ((D'.W ((1 : G) : G ⧸ K) i).subgroupOf K).map
          (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).rangeRestrict := by
  have := hG.isPretransitive
  have := faithfulSMul_quotient_of_normalCore_eq_bot hN
  have hO' : jOddCore G (G ⧸ K) = ⊥ := jOddCore_eq_bot_of_pPrimeCore_eq_bot hO
  have hiff := fun u : G => mem_longInvAt_one_quotient_iff hG hB hαK hK hN (u := u)
  have ht' : t ∈ longInvAt G (G ⧸ K) ((1 : G) : G ⧸ K) := (hiff t).mpr ⟨ht.1, hαK.le ht.2⟩
  have hK1 := D'.closure_longInv_stabilizer hO' ht'
  have hS : longInvAt G (G ⧸ K) ((1 : G) : G ⧸ K) =
      K.subtype '' {k : K | (k : G) ∈ longInv G Ω} := by
    ext u
    refine ⟨fun hu => ?_, ?_⟩
    · obtain ⟨h1, h2⟩ := (hiff u).mp hu
      exact ⟨⟨u, h2⟩, h1, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact (hiff k).mpr ⟨hk, k.2⟩
  have hWK : ∀ i, D'.W ((1 : G) : G ⧸ K) i ≤ K := fun i g hg => by
    have h1 := D'.smul_eq_of_mem_W hO' hg
    rwa [← mem_stabilizer_iff, MulAction.stabilizer_quotient] at h1
  have hJB : jHull (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).range
        (K ⧸ (stabilizer G α).subgroupOf K) =
      (Subgroup.closure {k : K | (k : G) ∈ longInv G Ω}).map
        (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).rangeRestrict := by
    rw [MonoidHom.map_closure, jHull]
    congr 1
    ext y
    refine ⟨fun hy => ?_, ?_⟩
    · obtain ⟨k, hk, hky⟩ := (mem_longInv_range_block_iff hG hαK.le (three_le_relIndex hG hαK)
        (holtTheorem1Below_range_block hB α hK) y).mp hy
      exact ⟨k, hk, Subtype.ext hky⟩
    · rintro ⟨k, hk, rfl⟩
      exact (mem_longInv_range_block_iff hG hαK.le (three_le_relIndex hG hαK)
        (holtTheorem1Below_range_block hB α hK) _).mpr ⟨k, hk, rfl⟩
  have hcl : Subgroup.closure {k : K | (k : G) ∈ longInv G Ω} =
      Subgroup.zpowers (⟨t, hαK.le ht.2⟩ : K) ⊔
        ⨆ i, (D'.W ((1 : G) : G ⧸ K) i).subgroupOf K := by
    apply Subgroup.map_injective K.subtype_injective
    rw [MonoidHom.map_closure, ← hS, hK1, Subgroup.map_sup, MonoidHom.map_zpowers,
      Subgroup.map_iSup]
    congr 1
    exact iSup_congr fun i => by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hWK i)]
  rw [hJB, hcl, Subgroup.map_sup, MonoidHom.map_zpowers, Subgroup.map_iSup]

omit [FaithfulSMul G Ω] in
theorem holtStructure_quotient_of_normalCore_eq_bot (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω)) {α : Ω} {K : Subgroup G}
    (hαK : stabilizer G α < K) (hK : K ≠ ⊤) (hN : K.normalCore = ⊥) :
    HoltStructure G (G ⧸ K) := by
  obtain ⟨D⟩ := holtStructure_range_quotient hG hB hαK hK
  have hinj : Function.Injective (toPermHom G (G ⧸ K)) := by
    rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.normalCore_eq_ker, hN]
  exact ⟨D.comap (e := Equiv.refl (G ⧸ K)) (MonoidHom.rangeRestrict_injective_iff.mpr hinj)
    (fun _ _ => rfl) fun y _ => MonoidHom.rangeRestrict_surjective _ y⟩

end KernelTrivial

section KernelTrivialFalse

variable {G : Type} [Group G] [Finite G] {Ω : Type} [MulAction G Ω] [Finite Ω]
  [FaithfulSMul G Ω]

omit [FaithfulSMul G Ω] in
theorem false_of_kernel_eq_bot (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω)) (hO : CFSG.pPrimeCore 2 G = ⊥)
    {α : Ω} {K : Subgroup G} (hαK : stabilizer G α < K) (hK : K ≠ ⊤)
    (hprim : IsPreprimitive (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).range
      (K ⧸ (stabilizer G α).subgroupOf K))
    (hN : K.normalCore = ⊥) : False := by
  classical
  have := hG.isPretransitive
  have := faithfulSMul_quotient_of_normalCore_eq_bot hN
  have hO' : jOddCore G (G ⧸ K) = ⊥ := jOddCore_eq_bot_of_pPrimeCore_eq_bot hO
  obtain ⟨D'⟩ := holtStructure_quotient_of_normalCore_eq_bot hG hB hαK hK hN
  obtain ⟨DB⟩ := holtStructure_range_block hG hB hαK hK
  obtain ⟨t, ht⟩ := hG.longInvAt_nonempty α
  have hHb := jHull_range_block_eq hG hB hO hαK hK hN D' ht
  set πB := (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).rangeRestrict with hπB
  set c₁ : G ⧸ K := ((1 : G) : G ⧸ K) with hc₁
  set Hb := jHull (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).range
    (K ⧸ (stabilizer G α).subgroupOf K) with hHbdef
  set tk : K := ⟨t, hαK.le ht.2⟩ with htk
  have hWK : ∀ i, D'.W c₁ i ≤ K := fun i g hg => by
    have h1 := D'.smul_eq_of_mem_W hO' hg
    rwa [← mem_stabilizer_iff, MulAction.stabilizer_quotient] at h1
  have ht' : t ∈ longInvAt G (G ⧸ K) c₁ :=
    (mem_longInvAt_one_quotient_iff hG hB hαK hK hN).mpr ⟨ht.1, hαK.le ht.2⟩
  have htN : ∀ i, πB tk ∈
      Subgroup.normalizer (((D'.W c₁ i).subgroupOf K).map πB : Set _) := by
    intro i
    have hn := D'.mem_normalizer_W (mem_jHull_of_mem_longInv ht'.1) ht'.2 (i := i)
    have hk : tk ∈ Subgroup.normalizer (((D'.W c₁ i).subgroupOf K : Subgroup K) : Set K) := by
      rw [Subgroup.mem_normalizer_iff] at hn ⊢
      intro h
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      exact hn h
    exact Subgroup.le_normalizer_map πB (Subgroup.mem_map_of_mem πB hk)
  have hcomm : ∀ i j, i ≠ j → ∀ x ∈ ((D'.W c₁ i).subgroupOf K).map πB,
      ∀ y ∈ ((D'.W c₁ j).subgroupOf K).map πB, x * y = y * x := by
    rintro i j hij _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (D'.commute_of_mem_W_of_ne hO' hij ha hb)
  have hnorm : ∀ i, Hb ≤ Subgroup.normalizer (((D'.W c₁ i).subgroupOf K).map πB : Set _) := by
    intro i
    rw [hHb]
    refine sup_le ((Subgroup.zpowers_le).mpr (htN i)) (iSup_le fun j => ?_)
    by_cases hji : j = i
    · subst hji
      exact Subgroup.le_normalizer
    · refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact hcomm i j (Ne.symm hji) x hx y hy
  set P := ⨆ i, ((D'.W c₁ i).subgroupOf K).map πB with hPdef
  have hPH : P ≤ Hb := by rw [hHb]; exact le_sup_right
  have hWbH : ∀ i, ((D'.W c₁ i).subgroupOf K).map πB ≤ Hb := fun i =>
    (le_iSup (fun i => ((D'.W c₁ i).subgroupOf K).map πB) i).trans hPH
  have htbH : πB tk ∈ Hb := by rw [hHb]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht.1.1]; exact pow_orderOf_eq_one t
  have htb2 : πB tk * πB tk = 1 := by
    rw [← map_mul, show tk * tk = 1 from Subtype.ext ht2, map_one]
  have hPnorm : ∀ b ∈ Hb, ∀ p ∈ P, b * p * b⁻¹ ∈ P := fun b hb p hp =>
    (Subgroup.mem_normalizer_iff.mp (mem_normalizer_iSup fun i => hnorm i hb) p).mp hp
  have hcommP : ⁅Hb, Hb⁆ ≤ P :=
    commutator_le_of_relIndex_le_two (relIndex_le_two_of_sup_zpowers htb2 hPH htbH hPnorm hHb.symm)
  have halt : ∀ i, ¬ IsNaturalSE (D'.M i) →
      D'.M i = alternatingGroup (D'.Ψc i) ∧ 7 ≤ Fintype.card (D'.Ψc i) ∧
        IsSimpleGroup ((D'.W c₁ i).subgroupOf K) ∧
        ⁅((D'.W c₁ i).subgroupOf K).map πB, ((D'.W c₁ i).subgroupOf K).map πB⁆ =
          ((D'.W c₁ i).subgroupOf K).map πB := by
    intro i hi
    obtain ⟨hM, h7⟩ := (D'.factor i).resolve_right hi
    have e := Subgroup.subgroupOfEquivOfLe (hWK i)
    have := D'.isSimpleGroup_W_of_alternatingGroup hO' c₁ hM h7
    have := D'.isPerfect_W_of_alternatingGroup hO' c₁ hM h7
    have hpk : Group.IsPerfect ((D'.W c₁ i).subgroupOf K) :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    refine ⟨hM, h7, e.isSimpleGroup, ?_⟩
    rw [← Subgroup.map_commutator, Subgroup.isPerfect_iff.mp hpk]
  have hse : ∀ i, IsNaturalSE (D'.M i) →
      IsPGroup 2 (((D'.W c₁ i).subgroupOf K).map πB) ∧
        ∀ x ∈ ((D'.W c₁ i).subgroupOf K).map πB,
          ∀ y ∈ ((D'.W c₁ i).subgroupOf K).map πB, x * y = y * x := by
    intro i hi
    refine ⟨(isPGroup_two_of_mul_self_eq_one fun w hw =>
      Subtype.ext (D'.mul_self_eq_one_of_mem_W hO' hi hw)).map πB, ?_⟩
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (D'.commute_of_mem_W hO' hi ha hb)
  have hnt : Nontrivial (K ⧸ (stabilizer G α).subgroupOf K) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    have := three_le_relIndex hG hαK
    change 1 < (stabilizer G α).relIndex K
    omega
  have hnotrans : ¬ IsPretransitive (⊥ : Subgroup
      (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).range)
      (K ⧸ (stabilizer G α).subgroupOf K) := by
    intro hT
    obtain ⟨c, c', hcc'⟩ := exists_pair_ne (K ⧸ (stabilizer G α).subgroupOf K)
    obtain ⟨o, ho⟩ := exists_smul_eq (⊥ : Subgroup
      (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).range) c c'
    have ho1 : o = 1 := Subtype.ext ((Subgroup.mem_bot).mp o.2)
    rw [ho1, one_smul] at ho
    exact hcc' ho
  by_cases hfix : fixedPoints (jOddCore (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).range
      (K ⧸ (stabilizer G α).subgroupOf K)) (K ⧸ (stabilizer G α).subgroupOf K) = Set.univ
  ·
    have hObot : jOddCore (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).range
        (K ⧸ (stabilizer G α).subgroupOf K) = ⊥ := by
      rw [eq_bot_iff]
      intro o ho
      have h1 : ∀ c, o • c = c := fun c =>
        (mem_fixedPoints.mp (hfix ▸ Set.mem_univ c : c ∈ _)) ⟨o, ho⟩
      exact (Subgroup.mem_bot).mpr (Subtype.ext (Equiv.ext h1))
    obtain ⟨j⟩ : Nonempty DB.ι := by
      by_contra hc
      rw [not_nonempty_iff] at hc
      have hT := (DB.isEmpty_ι_iff).mp hc
      rw [hObot] at hT
      exact hnotrans hT
    have hLH : DB.L j ≤ Hb := DB.L_le j
    have hsub : (⊥ : Subgroup (DB.L j)) = (jOddCore (toPermHom K
        (K ⧸ (stabilizer G α).subgroupOf K)).range
        (K ⧸ (stabilizer G α).subgroupOf K)).subgroupOf (DB.L j) := by
      rw [hObot, Subgroup.bot_subgroupOf]
    let eL : DB.L j ≃* DB.M j := (QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq hsub)).trans (DB.quotientEquivM j)
    have := DB.isSimpleGroup_M j
    have := DB.isPerfect_M j
    have hLs : IsSimpleGroup (DB.L j) := eL.isSimpleGroup
    have hLp : ⁅DB.L j, DB.L j⁆ = DB.L j := Subgroup.isPerfect_iff.mp
      (Group.IsPerfect.ofSurjective (f := eL.symm.toMonoidHom) eL.symm.surjective)
    have hLc : ¬ IsMulCommutative (DB.L j) := fun h => DB.not_isMulCommutative_M j
      ⟨⟨fun a b => eL.symm.injective (by
        rw [map_mul, map_mul]; exact h.is_comm.comm _ _)⟩⟩
    have hLbot : DB.L j ≠ ⊥ := fun h => by
      obtain ⟨x, hx⟩ := exists_ne (1 : DB.L j)
      exact hx (Subtype.ext ((Subgroup.mem_bot).mp (h ▸ x.2)))
    have hLP : DB.L j ≤ P := by
      rw [← hLp]
      exact (Subgroup.commutator_mono hLH hLH).trans hcommP
    have hLnorm : ∀ x ∈ Hb, ∀ l ∈ DB.L j, x * l * x⁻¹ ∈ DB.L j := fun x hx l hl =>
      (Subgroup.mem_normalizer_iff.mp (DB.le_normalizer j hx) l).mp hl
    have key : ∀ i, ((D'.W c₁ i).subgroupOf K).map πB ⊓ DB.L j = ⊥ ∨
        DB.L j ≤ ((D'.W c₁ i).subgroupOf K).map πB := fun i =>
      inf_eq_bot_or_le_of_isSimpleGroup fun l hl v hv =>
        (Subgroup.mem_normalizer_iff.mp (hnorm i (hLH hl)) v).mp hv
    by_cases hex : ∃ i, DB.L j ≤ ((D'.W c₁ i).subgroupOf K).map πB
    · obtain ⟨i, hi⟩ := hex
      have hiSE : ¬ IsNaturalSE (D'.M i) := fun h => hLc
        ⟨⟨fun a b => Subtype.ext ((hse i h).2 a (hi a.2) b (hi b.2))⟩⟩
      obtain ⟨hM, h7, hs, -⟩ := halt i hiSE
      rcases map_eq_bot_or_injective_of_isSimpleGroup πB
          (W := (D'.W c₁ i).subgroupOf K) with h | hinj
      · exact hLbot (le_bot_iff.mp (h ▸ hi))
      have hrange : (πB.comp ((D'.W c₁ i).subgroupOf K).subtype).range =
          ((D'.W c₁ i).subgroupOf K).map πB := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
      let e3 : (D'.W c₁ i).subgroupOf K ≃* ((D'.W c₁ i).subgroupOf K).map πB :=
        (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
      have hWs : IsSimpleGroup (((D'.W c₁ i).subgroupOf K).map πB) := e3.symm.isSimpleGroup
      have hLeq : DB.L j = ((D'.W c₁ i).subgroupOf K).map πB := by
        rcases inf_eq_bot_or_le_of_isSimpleGroup (L := ((D'.W c₁ i).subgroupOf K).map πB)
            (V := DB.L j) (fun l hl v hv => hLnorm l (hWbH i hl) v hv) with h | h
        · exact absurd (by rwa [inf_eq_left.mpr hi] at h) hLbot
        · exact le_antisymm hi h
      let f : DB.M j ≃* (alternatingGroup (D'.Ψc i) ⊓
          stabilizer (Equiv.Perm (D'.Ψc i)) (D'.coord c₁ i) : Subgroup _) :=
        eL.symm.trans ((MulEquiv.subgroupCongr hLeq).trans (e3.symm.trans
          ((Subgroup.subgroupOfEquivOfLe (hWK i)).trans ((D'.wEquiv hO' c₁ i).trans
            (MulEquiv.subgroupCongr (D'.wModel_eq_of_alternatingGroup c₁ hM h7))))))
      rcases DB.factor j with ⟨hMj, h7j⟩ | hSE
      · have hc := card_eq_of_mulEquiv_alternatingGroup_inf_stabilizer (by omega) (by omega)
          (f.symm.trans (MulEquiv.subgroupCongr hMj))
        obtain ⟨a, ha⟩ := D'.odd_card_Ψc i
        obtain ⟨b, hb⟩ := DB.odd_card_Ψc j
        omega
      · have h6 : 6 ≤ Fintype.card {x // x ≠ D'.coord c₁ i} := by
          rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
          omega
        exact (hSE.not_mulEquiv_alternatingGroup h6).false
          (f.trans (alternatingGroupStabilizerEquiv (D'.coord c₁ i)).symm)
    · push Not at hex
      have hcent : P ≤ Subgroup.centralizer (DB.L j : Set _) := iSup_le fun i y hy => by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have hi := (key i).resolve_right (hex i)
        exact commute_of_inf_eq_bot (fun b hb a ha => hLnorm b (hWbH i hb) a ha)
          (fun a ha b hb => (Subgroup.mem_normalizer_iff.mp (hnorm i (hLH ha)) b).mp hb)
          (by rwa [inf_comm] at hi) hx hy
      exact hLc ⟨⟨fun a b => Subtype.ext
        (Subgroup.mem_centralizer_iff.mp (hcent (hLP b.2)) a a.2)⟩⟩
  ·
    have hT := IsQuasiPreprimitive.isPretransitive_of_normal hfix
    have hempty : IsEmpty DB.ι := (DB.isEmpty_ι_iff).mpr hT
    have hsup : Hb = jOddCore (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).range
        (K ⧸ (stabilizer G α).subgroupOf K) ⊔ Subgroup.zpowers DB.t := by
      have h := DB.sup_eq
      rw [iSup_of_empty, sup_bot_eq] at h
      exact h.symm
    have hcO := commutator_le_of_relIndex_le_two
      (relIndex_jOddCore_jHull_eq_two DB.t_mem.1 hsup).le
    have hbot : ∀ i, ¬ IsNaturalSE (D'.M i) → ((D'.W c₁ i).subgroupOf K).map πB = ⊥ := by
      intro i hi
      obtain ⟨hM, h7, hs, hp⟩ := halt i hi
      rcases map_eq_bot_or_injective_of_isSimpleGroup πB
          (W := (D'.W c₁ i).subgroupOf K) with h | hinj
      · exact h
      exfalso
      have hle : ((D'.W c₁ i).subgroupOf K).map πB ≤
          jOddCore (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).range
            (K ⧸ (stabilizer G α).subgroupOf K) := by
        rw [← hp]
        exact (Subgroup.commutator_mono (hWbH i) (hWbH i)).trans hcO
      have hodd := Odd.of_dvd_nat odd_card_jOddCore (Subgroup.card_dvd_of_le hle)
      have hrange : (πB.comp ((D'.W c₁ i).subgroupOf K).subtype).range =
          ((D'.W c₁ i).subgroupOf K).map πB := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
      rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hWK i)).toEquiv] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) (D'.even_card_W hO' c₁ hM h7)
    have hP2 : IsPGroup 2 P := isPGroup_iSup_of_commute (fun i => by
      by_cases h : IsNaturalSE (D'.M i)
      · exact (hse i h).1
      · rw [hbot i h]
        exact IsPGroup.of_bot) hcomm
    have hH2 : IsPGroup 2 Hb := by
      rw [hHb]
      refine IsPGroup.to_sup_of_normal_right' (isPGroup_two_of_mul_self_eq_one fun w hw => ?_)
        hP2 ((Subgroup.zpowers_le).mpr (mem_normalizer_iSup fun i => htN i))
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, htb2, one_zpow]
    have hO2 := hH2.to_le (jOddCore_le_jHull (G := (toPermHom K
      (K ⧸ (stabilizer G α).subgroupOf K)).range) (Ω := K ⧸ (stabilizer G α).subgroupOf K))
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hO2
    have hodd := odd_card_jOddCore (G := (toPermHom K
      (K ⧸ (stabilizer G α).subgroupOf K)).range) (Ω := K ⧸ (stabilizer G α).subgroupOf K)
    rw [hn] at hodd
    have hn0 : n = 0 := by
      by_contra hn0
      exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_pow' hn0).mpr even_two)
    have hObot := Subgroup.eq_bot_of_card_eq _ (by rw [hn, hn0, pow_zero])
    rw [hObot] at hT
    exact hnotrans hT

end KernelTrivialFalse

section Components

theorem le_of_relIndex_le_two_of_odd {X : Type*} [Group X] [Finite X] {A B : Subgroup X}
    (h2 : A.relIndex B ≤ 2) (hodd : Odd (Nat.card B)) : B ≤ A := by
  have hd := Subgroup.relIndex_dvd_card A B
  have h0 : A.relIndex B ≠ 0 :=
    (Subgroup.index_ne_zero_of_finite : (A.subgroupOf B).index ≠ 0)
  apply Subgroup.relIndex_eq_one.mp
  rcases (by omega : A.relIndex B = 1 ∨ A.relIndex B = 2) with h | h
  · exact h
  · rw [h] at hd
    exact absurd hd (Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hodd))

variable {X : Type*} [Group X] {Δ : Type*} [MulAction X Δ]

noncomputable def HoltData.equivMOfOddCoreEqBot (D : HoltData X Δ) (hO : jOddCore X Δ = ⊥)
    (i : D.ι) : D.L i ≃* D.M i :=
  (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq
    (by rw [hO, Subgroup.bot_subgroupOf]))).trans (D.quotientEquivM i)

theorem HoltData.isSimpleGroup_L (D : HoltData X Δ) (hO : jOddCore X Δ = ⊥) (i : D.ι) :
    IsSimpleGroup (D.L i) :=
  have := D.isSimpleGroup_M i
  (D.equivMOfOddCoreEqBot hO i).isSimpleGroup

theorem HoltData.commutator_L_eq (D : HoltData X Δ) (hO : jOddCore X Δ = ⊥) (i : D.ι) :
    ⁅D.L i, D.L i⁆ = D.L i :=
  have := D.isPerfect_M i
  Subgroup.isPerfect_iff.mp (Group.IsPerfect.ofSurjective
    (f := (D.equivMOfOddCoreEqBot hO i).symm.toMonoidHom)
    (D.equivMOfOddCoreEqBot hO i).symm.surjective)

end Components

section PrimitiveData

variable {X : Type*} [Group X] {Δ : Type*} [MulAction X Δ]

theorem HoltData.eq_one_of_forall_commute_L [FaithfulSMul X Δ] (D : HoltData X Δ)
    (hO : jOddCore X Δ = ⊥) {c : X} (hc : ∀ j, ∀ y ∈ D.L j, c * y = y * c) : c = 1 := by
  apply eq_of_smul_eq_smul (α := Δ)
  intro β
  rw [one_smul]
  by_contra hne
  have hcoord : D.coord (c • β) ≠ D.coord β := fun h => hne (D.coord_injective hO h)
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hcoord
  obtain ⟨m, hm, hmβ, hmγ⟩ := (D.factor j).exists_mem_apply_eq_apply_ne hj
  obtain ⟨h, hhL, rfl⟩ := D.mem_M.mp hm
  have hfixβ : (h : X) • β = β := D.coord_injective hO (funext fun k => by
    by_cases hk : k = j
    · subst hk
      rw [D.coord_smul]
      exact hmβ
    · rw [D.coord_smul, D.rho_eq_one_of_mem_L (Ne.symm hk) hhL, Equiv.Perm.one_apply])
  apply hmγ
  rw [← D.coord_smul, ← mul_smul, ← hc j h hhL, mul_smul, hfixβ]

theorem HoltData.eq_empty_of_finsetSup_normal [FaithfulSMul X Δ] [IsPreprimitive X Δ]
    (D : HoltData X Δ) (hO : jOddCore X Δ = ⊥) {s : Finset D.ι} (hs : (s.sup D.L).Normal)
    {j : D.ι} (hj : j ∉ s) : s = ∅ := by
  by_contra hne
  obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  by_cases hfix : fixedPoints ↥(s.sup D.L) Δ = Set.univ
  · have hLk : D.L k = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have hy' : y ∈ s.sup D.L := Finset.le_sup (f := D.L) hk hy
      refine (Subgroup.mem_bot).mpr (eq_of_smul_eq_smul (α := Δ) fun δ => ?_)
      rw [one_smul]
      exact (mem_fixedPoints.mp (hfix ▸ Set.mem_univ δ : δ ∈ _)) ⟨y, hy'⟩
    have := D.isSimpleGroup_L hO k
    obtain ⟨x, hx⟩ := exists_ne (1 : D.L k)
    exact hx (Subtype.ext ((Subgroup.mem_bot).mp (hLk ▸ x.2)))
  · have hT := IsQuasiPreprimitive.isPretransitive_of_normal hfix
    obtain ⟨ω, -⟩ := D.t_mem.2
    have : Nontrivial (D.Ψc j) := by
      rw [← Fintype.one_lt_card_iff_nontrivial]
      have := D.five_le_card j
      omega
    obtain ⟨b, hb⟩ := exists_ne (D.coord ω j)
    obtain ⟨ω', hω'⟩ := D.exists_coord_eq_update ω j b
    obtain ⟨y, hy⟩ := exists_smul_eq ↥(s.sup D.L) ω ω'
    have hmem : ω' ∈ orbit (jOddCore X Δ ⊔ s.sup D.L : Subgroup X) ω :=
      ⟨⟨y, Subgroup.mem_sup_right y.2⟩, hy⟩
    have h1 := (D.mem_orbit_sup_finsetSup_iff s ω ω').mp hmem j hj
    rw [hω', Function.update_self] at h1
    exact hb h1

theorem HoltData.iSup_L_normal (D : HoltData X Δ) : (⨆ i, D.L i).Normal := by
  refine ⟨fun y hy g => ?_⟩
  obtain ⟨σ, hσ⟩ := D.conj_L g
  have hle : (⨆ i, D.L i).map (MulAut.conj g).toMonoidHom ≤ ⨆ i, D.L i := by
    rw [Subgroup.map_iSup]
    exact iSup_le fun i => (hσ i).symm.le.trans (le_iSup D.L (σ i))
  exact hle ⟨y, hy, rfl⟩

end PrimitiveData

section KernelSocle

variable {G : Type} [Group G] [Finite G] {Ω : Type} [MulAction G Ω] [Finite Ω]
  [FaithfulSMul G Ω]

omit [Finite G] [Finite Ω] [FaithfulSMul G Ω] in
theorem blockKernelHom_conjNormal {α : Ω} {K : Subgroup G} (k : K) (x : K.normalCore) :
    blockKernelHom G α K (MulAut.conjNormal (k : G) x) =
      (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).rangeRestrict k *
        blockKernelHom G α K x *
          ((toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).rangeRestrict k)⁻¹ := by
  have h : Subgroup.inclusion K.normalCore_le (MulAut.conjNormal (k : G) x) =
      k * Subgroup.inclusion K.normalCore_le x * k⁻¹ := Subtype.ext rfl
  simp only [blockKernelHom, MonoidHom.coe_comp, Function.comp_apply, h, map_mul, map_inv]

theorem exists_component_of_kernel_ne_bot (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω)) (hH : jHull G Ω = ⊤)
    (hO : CFSG.pPrimeCore 2 G = ⊥) {α : Ω} {K : Subgroup G} (hαK : stabilizer G α < K)
    (hK : K ≠ ⊤)
    (hprim : IsPreprimitive (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).range
      (K ⧸ (stabilizer G α).subgroupOf K))
    (hN : K.normalCore ≠ ⊥)
    (hT : ¬ IsPretransitive (jOddCore (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).range
      (K ⧸ (stabilizer G α).subgroupOf K)) (K ⧸ (stabilizer G α).subgroupOf K)) :
    ∃ (D : HoltData (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).range
        (K ⧸ (stabilizer G α).subgroupOf K)) (j₀ : D.ι), (∀ j, j = j₀) ∧
      jOddCore (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).range
        (K ⧸ (stabilizer G α).subgroupOf K) = ⊥ ∧
      D.L j₀ ≤ (blockKernelHom G α K).range ∧
      (((D.L j₀).comap (blockKernelHom G α K)).map K.normalCore.subtype).Normal := by
  classical
  obtain ⟨D⟩ := holtStructure_range_block hG hB hαK hK
  have hκ := blockKernelHom_injective hG hαK.le hO
  have hκN := blockKernelHom_range_normal α K
  have hOB : jOddCore (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).range
      (K ⧸ (stabilizer G α).subgroupOf K) = ⊥ := by
    by_contra hne
    refine hT (IsQuasiPreprimitive.isPretransitive_of_normal fun hfix => hne ?_)
    rw [eq_bot_iff]
    intro o ho
    refine (Subgroup.mem_bot).mpr (Subtype.ext (Equiv.ext fun c => ?_))
    exact (mem_fixedPoints.mp (hfix ▸ Set.mem_univ c : c ∈ _)) ⟨o, ho⟩
  have hLs := D.isSimpleGroup_L hOB
  have hex : ∃ j, D.L j ≤ (blockKernelHom G α K).range := by
    by_contra hnone
    push Not at hnone
    have hVn : ((blockKernelHom G α K).range ⊓ jHull (toPermHom K
        (K ⧸ (stabilizer G α).subgroupOf K)).range (K ⧸ (stabilizer G α).subgroupOf K)).Normal :=
      Subgroup.normal_inf_normal _ _
    have hVL : ∀ j, ((blockKernelHom G α K).range ⊓ jHull (toPermHom K
        (K ⧸ (stabilizer G α).subgroupOf K)).range (K ⧸ (stabilizer G α).subgroupOf K)) ⊓
          D.L j = ⊥ := fun j => by
      have := hLs j
      exact (inf_eq_bot_or_le_of_isSimpleGroup (L := D.L j)
        (fun l _ v hv => hVn.conj_mem v hv l)).resolve_right
          fun h => hnone j (h.trans inf_le_left)
    have hV : (blockKernelHom G α K).range ⊓ jHull (toPermHom K
        (K ⧸ (stabilizer G α).subgroupOf K)).range (K ⧸ (stabilizer G α).subgroupOf K) = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      refine (Subgroup.mem_bot).mpr (D.eq_one_of_forall_commute_L hOB fun j y hy => ?_)
      exact commute_of_inf_eq_bot (fun b _ a ha => hVn.conj_mem a ha b)
        (fun a ha b hb => (Subgroup.mem_normalizer_iff.mp (D.le_normalizer j ha.2) b).mp hb)
        (hVL j) hv hy
    apply hN
    rw [eq_bot_iff]
    intro n hn
    have h1 : blockKernelHom G α K ⟨n, hn⟩ = 1 := D.eq_one_of_forall_commute_L hOB
      fun j y hy => commute_of_inf_eq_bot (fun b _ a ha => hκN.conj_mem a ha b)
        (fun a _ b hb => (jHull_normal).conj_mem b hb a) hV ⟨_, rfl⟩ (D.L_le j hy)
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val (hκ (h1.trans (map_one _).symm)))
  obtain ⟨j₁, hj₁⟩ := hex
  have hall : ∀ k, D.L k ≤ (blockKernelHom G α K).range := by
    by_contra hnot
    push Not at hnot
    obtain ⟨k, hk⟩ := hnot
    have hs : ((Finset.univ.filter fun k => ¬ D.L k ≤ (blockKernelHom G α K).range).sup
        D.L).Normal := by
      refine ⟨fun y hy g => ?_⟩
      obtain ⟨σ, hσ⟩ := D.conj_L g
      have hle : ((Finset.univ.filter fun k => ¬ D.L k ≤ (blockKernelHom G α K).range).sup
          D.L).map (MulAut.conj g).toMonoidHom ≤
            (Finset.univ.filter fun k => ¬ D.L k ≤ (blockKernelHom G α K).range).sup D.L := by
        rw [Subgroup.map_le_iff_le_comap]
        refine Finset.sup_le fun i hi => ?_
        rw [← Subgroup.map_le_iff_le_comap, ← hσ i]
        refine Finset.le_sup (f := D.L) ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        intro hσi
        apply hi
        intro y hy
        have h1 := hσi (by rw [hσ i]; exact ⟨y, hy, rfl⟩ :
          (MulAut.conj g).toMonoidHom y ∈ D.L (σ i))
        have h2 := hκN.conj_mem _ h1 g⁻¹
        simpa [mul_assoc] using h2
      exact hle ⟨y, hy, rfl⟩
    have hs0 := D.eq_empty_of_finsetSup_normal hOB hs (j := j₁) (by simp [hj₁])
    have hk' : k ∈ Finset.univ.filter fun k => ¬ D.L k ≤ (blockKernelHom G α K).range := by
      simp [hk]
    rw [hs0] at hk'
    exact absurd hk' (Finset.notMem_empty k)
  have hmapC : ∀ k, ((D.L k).comap (blockKernelHom G α K)).map (blockKernelHom G α K) = D.L k :=
    fun k => Subgroup.map_comap_eq_self (hall k)
  have hCs : (⨆ k, D.L k).comap (blockKernelHom G α K) =
      ⨆ k, (D.L k).comap (blockKernelHom G α K) := by
    apply Subgroup.map_injective hκ
    rw [Subgroup.map_comap_eq_self (iSup_le hall), Subgroup.map_iSup]
    exact (iSup_congr hmapC).symm
  have hCsimple : ∀ k, IsSimpleGroup ((D.L k).comap (blockKernelHom G α K)) := fun k => by
    have := hLs k
    exact (((D.L k).comap (blockKernelHom G α K)).equivMapOfInjective _ hκ |>.trans
      (MulEquiv.subgroupCongr (hmapC k))).isSimpleGroup
  have hCperf : ∀ k, ⁅(D.L k).comap (blockKernelHom G α K),
      (D.L k).comap (blockKernelHom G α K)⁆ = (D.L k).comap (blockKernelHom G α K) := fun k =>
    Subgroup.map_injective hκ (by rw [Subgroup.map_commutator, hmapC, D.commutator_L_eq hOB])
  have hCsN : ((⨆ k, D.L k).comap (blockKernelHom G α K)).Normal :=
    D.iSup_L_normal.comap _
  have hCnorm : ∀ k, ∀ m ∈ (⨆ k, D.L k).comap (blockKernelHom G α K),
      ∀ l ∈ (D.L k).comap (blockKernelHom G α K),
        m * l * m⁻¹ ∈ (D.L k).comap (blockKernelHom G α K) := by
    intro k m hm l hl
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    have hmH := (iSup_le fun i => D.L_le i) hm
    exact (Subgroup.mem_normalizer_iff.mp (D.le_normalizer k hmH) _).mp hl
  have hCC : ∀ n : K.normalCore,
      (∀ x ∈ (⨆ k, D.L k).comap (blockKernelHom G α K), n * x = x * n) → n = 1 := by
    intro n hn
    apply hκ
    rw [map_one]
    refine D.eq_one_of_forall_commute_L hOB fun j y hy => ?_
    rw [← hmapC j] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [← map_mul, ← map_mul, hn x (Subgroup.comap_mono (le_iSup D.L j) hx)]
  have hmapmap : ∀ (g h : G) (C : Subgroup K.normalCore),
      (C.map (MulAut.conjNormal h).toMonoidHom).map (MulAut.conjNormal g).toMonoidHom =
        C.map (MulAut.conjNormal (g * h)).toMonoidHom := by
    intro g h C
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conjNormal_apply, mul_assoc]
  have hmapone : ∀ C : Subgroup K.normalCore,
      C.map (MulAut.conjNormal (1 : G)).toMonoidHom = C := by
    intro C
    convert Subgroup.map_id C
    ext x
    simp
  have hinv : ∀ g : G, (⨆ k, D.L k).comap (blockKernelHom G α K) ≤
      ((⨆ k, D.L k).comap (blockKernelHom G α K)).map (MulAut.conjNormal g).toMonoidHom := by
    intro g
    have hVn : (((⨆ k, D.L k).comap (blockKernelHom G α K)).map
        (MulAut.conjNormal g).toMonoidHom).Normal :=
      hCsN.map _ (MulAut.conjNormal g).surjective
    have hVC : ∀ n : K.normalCore, (∀ v ∈ ((⨆ k, D.L k).comap (blockKernelHom G α K)).map
        (MulAut.conjNormal g).toMonoidHom, n * v = v * n) → n = 1 := by
      intro n hn
      have h1 : (MulAut.conjNormal g).symm n = 1 := hCC _ fun x hx => by
        apply (MulAut.conjNormal g).injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        exact hn _ ⟨x, hx, rfl⟩
      rw [← (MulAut.conjNormal g).apply_symm_apply n, h1, map_one]
    conv_lhs => rw [hCs]
    exact iSup_le fun k => by
      have := hCsimple k
      exact le_of_forall_commute_eq_one (N := ⊤) (hCperf k)
        (Subgroup.comap_mono (le_iSup D.L k)) le_top le_top
        (fun n _ m hm => hCsN.conj_mem m hm n) (hCnorm k) (fun n _ v hv => hVn.conj_mem v hv n)
        (fun n _ hn => hVC n hn)
  have hCseq : ∀ g : G, ((⨆ k, D.L k).comap (blockKernelHom G α K)).map
      (MulAut.conjNormal g).toMonoidHom = (⨆ k, D.L k).comap (blockKernelHom G α K) := by
    intro g
    refine le_antisymm ?_ (hinv g)
    have h1 := Subgroup.map_mono (f := (MulAut.conjNormal g).toMonoidHom) (hinv g⁻¹)
    rwa [hmapmap, mul_inv_cancel, hmapone] at h1
  have hCle : ∀ k, (D.L k).comap (blockKernelHom G α K) ≤
      (⨆ k, D.L k).comap (blockKernelHom G α K) := fun k => Subgroup.comap_mono (le_iSup D.L k)
  have hperm : ∀ (g : G) k, ∃ k', ((D.L k).comap (blockKernelHom G α K)).map
      (MulAut.conjNormal g).toMonoidHom = (D.L k').comap (blockKernelHom G α K) := by
    intro g k
    have hSCs : ((D.L k).comap (blockKernelHom G α K)).map (MulAut.conjNormal g).toMonoidHom ≤
        (⨆ k, D.L k).comap (blockKernelHom G α K) :=
      (Subgroup.map_mono (hCle k)).trans (hCseq g).le
    have hSs : IsSimpleGroup (((D.L k).comap (blockKernelHom G α K)).map
        (MulAut.conjNormal g).toMonoidHom) := by
      have := hCsimple k
      exact (((D.L k).comap _).equivMapOfInjective _
        (MulAut.conjNormal g).injective).symm.isSimpleGroup
    have hSn : ∀ m ∈ (⨆ k, D.L k).comap (blockKernelHom G α K),
        ∀ s ∈ ((D.L k).comap (blockKernelHom G α K)).map (MulAut.conjNormal g).toMonoidHom,
          m * s * m⁻¹ ∈ ((D.L k).comap (blockKernelHom G α K)).map
            (MulAut.conjNormal g).toMonoidHom := by
      intro m hm s hs
      rw [← hCseq g] at hm
      obtain ⟨m', hm', rfl⟩ := hm
      obtain ⟨s', hs', rfl⟩ := hs
      exact ⟨m' * s' * m'⁻¹, hCnorm k m' hm' s' hs', by simp only [map_mul, map_inv]⟩
    by_cases hex : ∃ k', (D.L k').comap (blockKernelHom G α K) ≤
        ((D.L k).comap (blockKernelHom G α K)).map (MulAut.conjNormal g).toMonoidHom
    · obtain ⟨k', hk'⟩ := hex
      refine ⟨k', ?_⟩
      rcases inf_eq_bot_or_le_of_isSimpleGroup
          (V := (D.L k').comap (blockKernelHom G α K))
          (fun l hl v hv => hCnorm k' l (hSCs hl) v hv) with h | h
      · exfalso
        rw [inf_eq_left.mpr hk'] at h
        have := hCsimple k'
        obtain ⟨x, hx⟩ := exists_ne (1 : (D.L k').comap (blockKernelHom G α K))
        exact hx (Subtype.ext ((Subgroup.mem_bot).mp (h ▸ x.2)))
      · exact le_antisymm h hk'
    · push Not at hex
      exfalso
      have hcent : ∀ s ∈ ((D.L k).comap (blockKernelHom G α K)).map
          (MulAut.conjNormal g).toMonoidHom, s = 1 := fun s hs => hCC s fun x hx => by
        rw [hCs] at hx
        have hle : (⨆ k', (D.L k').comap (blockKernelHom G α K)) ≤ Subgroup.centralizer
            ((((D.L k).comap (blockKernelHom G α K)).map (MulAut.conjNormal g).toMonoidHom :
              Subgroup K.normalCore) : Set K.normalCore) := iSup_le fun k' => by
          have := hCsimple k'
          have hk'S := (inf_eq_bot_or_le_of_isSimpleGroup
            (L := (D.L k').comap (blockKernelHom G α K))
            (fun l hl v hv => hSn l (hCle k' hl) v hv)).resolve_right (hex k')
          intro y hy
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          exact commute_of_inf_eq_bot (fun b hb a ha => hSn b (hCle k' hb) a ha)
            (fun a ha b hb => hCnorm k' a (hSCs ha) b hb) hk'S hz hy
        exact Subgroup.mem_centralizer_iff.mp (hle hx) s hs
      obtain ⟨x, hx⟩ := exists_ne (1 : ((D.L k).comap (blockKernelHom G α K)).map
        (MulAut.conjNormal g).toMonoidHom)
      exact hx (Subtype.ext (hcent x x.2))
  have h1rel : 1 < (stabilizer G α).relIndex K := by
    have := three_le_relIndex hG hαK
    omega
  have hKC : ∀ u ∈ longInv G Ω, ∀ huK : u ∈ K, ∀ k,
      ((D.L k).comap (blockKernelHom G α K)).map (MulAut.conjNormal u).toMonoidHom =
        (D.L k).comap (blockKernelHom G α K) := by
    intro u hu huK k
    have := hG.isPretransitive
    have huH := mem_jHull_of_mem_longInv
      (rangeRestrict_mem_longInv_block hG.odd_card hαK.le h1rel huK hu)
    have hle : ((D.L k).comap (blockKernelHom G α K)).map (MulAut.conjNormal u).toMonoidHom ≤
        (D.L k).comap (blockKernelHom G α K) := by
      rintro _ ⟨x, hx, rfl⟩
      rw [Subgroup.mem_comap]
      change blockKernelHom G α K (MulAut.conjNormal ((⟨u, huK⟩ : K) : G) x) ∈ D.L k
      rw [blockKernelHom_conjNormal]
      exact (Subgroup.mem_normalizer_iff.mp (D.le_normalizer k huH) _).mp hx
    exact Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (f := (MulAut.conjNormal u).toMonoidHom)
        (MulAut.conjNormal u).injective])
  have hJC : ∀ u ∈ longInv G Ω, ∀ k,
      ((D.L k).comap (blockKernelHom G α K)).map (MulAut.conjNormal u).toMonoidHom =
        (D.L k).comap (blockKernelHom G α K) := by
    intro u hu k
    have := hG.isPretransitive
    obtain ⟨β, hβ, -⟩ := hu.2
    obtain ⟨g, rfl⟩ := exists_smul_eq G α β
    have hv := conj_mem_longInvAt ⟨hu, hβ⟩ g⁻¹
    rw [inv_inv, inv_smul_smul] at hv
    obtain ⟨k', hk'⟩ := hperm g⁻¹ k
    calc ((D.L k).comap (blockKernelHom G α K)).map (MulAut.conjNormal u).toMonoidHom
        = ((((D.L k).comap (blockKernelHom G α K)).map (MulAut.conjNormal g⁻¹).toMonoidHom).map
            (MulAut.conjNormal (g⁻¹ * u * g)).toMonoidHom).map
              (MulAut.conjNormal g).toMonoidHom := by
          rw [hmapmap, hmapmap, show g * (g⁻¹ * u * g) * g⁻¹ = u by group]
      _ = (D.L k).comap (blockKernelHom G α K) := by
          rw [hk', hKC _ hv.1 (hαK.le hv.2), ← hk', hmapmap, mul_inv_cancel, hmapone]
  have hGC : ∀ g : G, ∀ k,
      ((D.L k).comap (blockKernelHom G α K)).map (MulAut.conjNormal g).toMonoidHom =
        (D.L k).comap (blockKernelHom G α K) := by
    intro g k
    have hg : g ∈ Subgroup.closure (longInv G Ω) := by
      change g ∈ jHull G Ω
      rw [hH]
      exact Subgroup.mem_top g
    induction hg using Subgroup.closure_induction with
    | mem u hu => exact hJC u hu k
    | one => exact hmapone _
    | mul x y _ _ hx hy => rw [← hmapmap, hy, hx]
    | inv x _ hx =>
      conv_lhs => rw [← hx]
      rw [hmapmap, inv_mul_cancel, hmapone]
  have hLn : ∀ k, (D.L k).Normal := by
    intro k
    refine ⟨fun y hy γ => ?_⟩
    obtain ⟨k₀, hk₀⟩ := γ.2
    have hγ : (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).rangeRestrict k₀ = γ :=
      Subtype.ext hk₀
    rw [← hmapC k] at hy ⊢
    obtain ⟨x, hx, rfl⟩ := hy
    rw [← hγ, ← blockKernelHom_conjNormal]
    exact ⟨_, (hGC k₀ k).le ⟨x, hx, rfl⟩, rfl⟩
  have hsingle : ∀ j, j = j₁ := by
    intro j
    by_contra hj
    have hs : ((Finset.univ.erase j₁).sup D.L).Normal := by
      refine ⟨fun y hy g => ?_⟩
      have hle : ((Finset.univ.erase j₁).sup D.L).map (MulAut.conj g).toMonoidHom ≤
          (Finset.univ.erase j₁).sup D.L := by
        rw [Subgroup.map_le_iff_le_comap]
        refine Finset.sup_le fun i hi => ?_
        rw [← Subgroup.map_le_iff_le_comap]
        refine le_trans ?_ (Finset.le_sup (f := D.L) hi)
        rintro _ ⟨z, hz, rfl⟩
        exact (hLn i).conj_mem z hz g
      exact hle ⟨y, hy, rfl⟩
    have hs0 := D.eq_empty_of_finsetSup_normal hOB hs (j := j₁) (Finset.notMem_erase j₁ _)
    have hjm : j ∈ Finset.univ.erase j₁ := Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩
    rw [hs0] at hjm
    exact Finset.notMem_empty j hjm
  refine ⟨D, j₁, hsingle, hOB, hall j₁, ⟨fun y hy g => ?_⟩⟩
  obtain ⟨x, hx, rfl⟩ := hy
  exact ⟨_, (hGC g j₁).le ⟨x, hx, rfl⟩, by simp [MulAut.conjNormal_apply]⟩

end KernelSocle

end CFSG.Holt.H78
