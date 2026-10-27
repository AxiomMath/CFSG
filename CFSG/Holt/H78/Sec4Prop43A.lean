module

public import CFSG.Holt.H78.Sec4Defs
import CFSG.Holt.H78.Sec4Box
import CFSG.Holt.H78.Sec4CCLMatch
import CFSG.Holt.H78.DataSocle

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Open
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω}

namespace AltConfig

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem coe_γ_ne_left (hαβ : α ≠ β) (C : AltConfig G Ω α β) : (C.γ : Ω) ≠ α := fun h =>
  left_notMem_holtDelta (G := G) hαβ ((congrArg (· ∈ holtDelta G Ω α β) h).mp C.γ.2)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem coe_γ_ne_right (hαβ : α ≠ β) (C : AltConfig G Ω α β) : (C.γ : Ω) ≠ β := fun h =>
  right_notMem_holtDelta (G := G) hαβ ((congrArg (· ∈ holtDelta G Ω α β) h).mp C.γ.2)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem ncard_triple (hαβ : α ≠ β) (C : AltConfig G Ω α β) :
    ({α, β, (C.γ : Ω)} : Set Ω).ncard = 3 :=
  Set.ncard_eq_three.mpr ⟨α, β, C.γ, hαβ, (C.coe_γ_ne_left hαβ).symm,
    (C.coe_γ_ne_right hαβ).symm, rfl⟩

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem triple_subset_fixSet {γ : Ω} {Q : Subgroup G}
    (hQ : Q ≤ stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G γ) :
    ({α, β, γ} : Set Ω) ⊆ fixSet Ω Q := by
  rintro ω (rfl | rfl | rfl) <;> rw [mem_fixSet_iff_le_stabilizer]
  · exact hQ.trans (inf_le_left.trans inf_le_left)
  · exact hQ.trans (inf_le_left.trans inf_le_right)
  · exact hQ.trans inf_le_right

omit [Finite G] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem fixSet_eq_of_le (hαβ : α ≠ β) (C : AltConfig G Ω α β) {Q : Subgroup G}
    (hPQ : C.S ⊓ twoPointNormalizer G Ω α β (C.D.L C.i₁) ≤ Q)
    (hQ : Q ≤ stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G (C.γ : Ω)) :
    fixSet Ω Q = {α, β, (C.γ : Ω)} := by
  have hP : fixSet Ω (C.S ⊓ twoPointNormalizer G Ω α β (C.D.L C.i₁)) = {α, β, (C.γ : Ω)} := by
    refine (Set.eq_of_subset_of_ncard_le (triple_subset_fixSet (hPQ.trans hQ)) ?_
      (Set.toFinite _)).symm
    rw [C.ncard_triple hαβ, ← Nat.card_coe_set_eq, C.fix_three]
  exact Set.Subset.antisymm ((fixSet_anti hPQ).trans hP.le) (triple_subset_fixSet hQ)

omit [Finite G] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem fixSet_S (hαβ : α ≠ β) (C : AltConfig G Ω α β) : fixSet Ω C.S = {α, β, (C.γ : Ω)} :=
  C.fixSet_eq_of_le hαβ inf_le_left C.sylow.1

omit [FaithfulSMul G Ω] in
theorem exists_sylow (hS : Sec4Setting G Ω) (hαβ : α ≠ β) (C : AltConfig G Ω α β) :
    ∃ C' : AltConfig G Ω α β, C'.D = C.D ∧ HEq C'.i₁ C.i₁ ∧ C'.γ = C.γ ∧
      C.S ⊓ twoPointNormalizer G Ω α β (C.D.L C.i₁) ≤ C'.S ∧
      fusionIsSylowIn 2 (C'.S ⊓ twoPointNormalizer G Ω α β (C'.D.L C'.i₁))
        (stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G (C'.γ : Ω) ⊓
          twoPointNormalizer G Ω α β (C'.D.L C'.i₁)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N₁ := twoPointNormalizer G Ω α β (C.D.L C.i₁) with hN₁
  obtain ⟨P', hPP', hP'⟩ := exists_fusionIsSylowIn_ge (C.sylow.2.1.to_le inf_le_left)
    (inf_le_inf_right N₁ C.sylow.1)
  obtain ⟨S', hP'S', hS'⟩ := exists_fusionIsSylowIn_ge hP'.2.1 (hP'.1.trans inf_le_left)
  have hS'N : S' ⊓ N₁ = P' := hP'.2.2 _ (inf_le_inf_right N₁ hS'.1)
    (hS'.2.1.to_le inf_le_left) (le_inf hP'S' (hP'.1.trans inf_le_right))
  obtain ⟨-, w', hw', hw'γ, hw'S'⟩ := hS.sylow_twoPoint hαβ C.γ.2 hS'
  have hPS' : C.S ⊓ N₁ ≤ S' ⊓ N₁ := hS'N ▸ hPP'
  have hfix := C.fixSet_eq_of_le hαβ hPS' (inf_le_left.trans hS'.1)
  refine ⟨{ C with
      S := S'
      sylow := hS'
      w := w'
      w_mem := hw'
      w_fix := hw'γ
      w_comm := hw'S'
      fix_three := by rw [← hN₁, hfix, Nat.card_coe_set_eq, C.ncard_triple hαβ]
      fix_five := fun h5 => (C.fix_five h5).imp fun W hW => ⟨hW.1.trans hPS', hW.2⟩ },
    rfl, HEq.rfl, rfl, hPP'.trans hP'S', ?_⟩
  change fusionIsSylowIn 2 (S' ⊓ N₁)
    (stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G (C.γ : Ω) ⊓ N₁)
  rw [hS'N]
  exact hP'

omit [Finite G] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem fixSet_S_eq_triple (hαβ : α ≠ β) (C : AltConfig G Ω α β) {x y z : Ω}
    (hx : x ∈ fixSet Ω C.S) (hy : y ∈ fixSet Ω C.S) (hz : z ∈ fixSet Ω C.S) (hxy : x ≠ y)
    (hxz : x ≠ z) (hyz : y ≠ z) : fixSet Ω C.S = {x, y, z} := by
  refine (Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)).symm
  · rintro ω (rfl | rfl | rfl) <;> assumption
  · rw [C.fixSet_S hαβ, C.ncard_triple hαβ, Set.ncard_eq_three.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩]

omit [Finite G] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem mem_fixSet_S (hαβ : α ≠ β) (C : AltConfig G Ω α β) :
    α ∈ fixSet Ω C.S ∧ β ∈ fixSet Ω C.S ∧ (C.γ : Ω) ∈ fixSet Ω C.S := by
  rw [C.fixSet_S hαβ]
  exact ⟨Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩

omit [Finite G] [FaithfulSMul G Ω] in
theorem exists_mem_longInvAt_centralizer_swap (hS : Sec4Setting G Ω) (hαβ : α ≠ β)
    (C : AltConfig G Ω α β) {x y z : Ω} (hx : x ∈ fixSet Ω C.S) (hy : y ∈ fixSet Ω C.S)
    (hz : z ∈ fixSet Ω C.S) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ t ∈ longInvAt G Ω x, t ∈ Subgroup.centralizer (C.S : Set G) ∧ t • y = z ∧ t • z = y := by
  have hF := C.fixSet_S_eq_triple hαβ hx hy hz hxy hxz hyz
  have h3 : 3 ≤ Nat.card (fixSet Ω C.S) := by
    rw [Nat.card_coe_set_eq, C.fixSet_S hαβ, C.ncard_triple hαβ]
  obtain ⟨t, ht, htS⟩ := hS.star.star x C.S C.sylow.2.1 (mem_fixSet_iff_le_stabilizer.mp hx) h3
  have hfix : ∀ ω : Ω, t • ω = ω → ω = x := fun ω hω => ht.1.2.unique hω ht.2
  have htt : ∀ ω : Ω, t • t • ω = ω := fun ω => by
    rw [← mul_smul, ← sq, ← ht.1.1, pow_orderOf_eq_one, one_smul]
  have hty : t • y = z := by
    have h := smul_mem_fixSet_of_mem_normalizer (Subgroup.centralizer_le_normalizer _ htS) hy
    rw [hF, Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h | h
    · exact absurd (smul_left_cancel t (h.trans ht.2.symm)).symm hxy
    · exact absurd (hfix y h).symm hxy
    · exact h
  exact ⟨t, ht, htS, hty, by rw [← hty, htt]⟩

omit [FaithfulSMul G Ω] in
theorem holtDelta'_eq (hS : Sec4Setting G Ω) (hαβ : α ≠ β) (C : AltConfig G Ω α β)
    (h33 : ∀ γ ∈ holtDelta' G Ω α β,
      holtDelta' G Ω α β = orbit ↥(stabilizer G α ⊓ stabilizer G β) γ) :
    holtDelta' G Ω α β = holtDelta G Ω α β := by
  obtain ⟨hα, hβ, hγ⟩ := C.mem_fixSet_S hαβ
  obtain ⟨t, ht, -, htβ, -⟩ := C.exists_mem_longInvAt_centralizer_swap hS hαβ hα hβ hγ hαβ
    (C.coe_γ_ne_left hαβ).symm (C.coe_γ_ne_right hαβ).symm
  rw [h33 _ ⟨t, ht, htβ⟩, ← holtDelta_eq_orbit_of_mem C.γ.2]

end AltConfig

section Fibres

variable {K : Type*} [Group K] {X : Type*} [MulAction K X]

namespace HoltData

theorem smul_mem_orbit_jOddCore_iff_of_mem_L (D : HoltData K X) {k : D.ι} {l : jHull K X}
    (hl : (l : K) ∈ D.L k) (ω : X) :
    (l : K) • ω ∈ orbit (jOddCore K X) ω ↔ D.ρ k l (D.coord ω k) = D.coord ω k := by
  rw [← D.coord_eq_iff, ← D.coord_smul]
  constructor
  · intro h
    exact (congrFun h k).symm
  · intro h
    funext j
    by_cases hjk : j = k
    · subst hjk
      exact h.symm
    · rw [D.coord_smul, D.rho_eq_one_of_mem_L (Ne.symm hjk) hl, Equiv.Perm.one_apply]

theorem coord_eq_iff_forall_mem_L (D : HoltData K X) (k : D.ι) (a b : X) :
    D.coord a k = D.coord b k ↔ ∀ l : jHull K X, (l : K) ∈ D.L k →
      ((l : K) • a ∈ orbit (jOddCore K X) a ↔ (l : K) • b ∈ orbit (jOddCore K X) b) := by
  refine ⟨fun h l hl => by rw [D.smul_mem_orbit_jOddCore_iff_of_mem_L hl,
    D.smul_mem_orbit_jOddCore_iff_of_mem_L hl, h], fun h => ?_⟩
  refine ((D.factor k).eq_of_forall_apply_eq fun m hm hma => ?_).symm
  obtain ⟨l, hl, rfl⟩ := D.mem_M.mp hm
  exact (D.smul_mem_orbit_jOddCore_iff_of_mem_L hl b).mp
    ((h l hl).mp ((D.smul_mem_orbit_jOddCore_iff_of_mem_L hl a).mpr hma))

theorem coord_eq_iff_of_L_eq (D D' : HoltData K X) {i : D.ι} {k : D'.ι} (h : D.L i = D'.L k)
    (a b : X) : D.coord a i = D.coord b i ↔ D'.coord a k = D'.coord b k := by
  rw [D.coord_eq_iff_forall_mem_L, D'.coord_eq_iff_forall_mem_L, h]

theorem exists_equiv_coord_eq_iff_of_mulEquiv (D : HoltData K X) (φ : K ≃* K) (e : X ≃ X)
    (he : ∀ (g : K) (x : X), e (g • x) = φ g • e x) :
    ∃ σ : D.ι ≃ D.ι, ∀ i a b,
      D.coord a i = D.coord b i ↔ D.coord (e a) (σ i) = D.coord (e b) (σ i) := by
  obtain ⟨σ, hσ⟩ := exists_equiv_L_map D D φ e he
  refine ⟨σ, fun i a b => ?_⟩
  have hL : (D.congr φ e he).L i = D.L (σ i) := (D.congr_L φ e he i).trans (hσ i).symm
  rw [← D.congr_coord_apply φ e he a, ← D.congr_coord_apply φ e he b]
  exact coord_eq_iff_of_L_eq (D.congr φ e he) D hL (e a) (e b)

theorem exists_equiv_coord_eq_iff_of_mem_normalizer {X : Type*} {K : Subgroup (Equiv.Perm X)}
    (D : HoltData K X) {π : Equiv.Perm X}
    (hπ : π ∈ Subgroup.normalizer (K : Set (Equiv.Perm X))) :
    ∃ σ : D.ι ≃ D.ι, ∀ i a b,
      D.coord a i = D.coord b i ↔ D.coord (π a) (σ i) = D.coord (π b) (σ i) := by
  have hmem : ∀ k : Equiv.Perm X, k ∈ K ↔ π * k * π⁻¹ ∈ K := Subgroup.mem_normalizer_iff.mp hπ
  let φ : K ≃* K :=
    { toFun := fun k => ⟨π * k * π⁻¹, (hmem k).mp k.2⟩
      invFun := fun k => ⟨π⁻¹ * k * π, (hmem _).mpr (by simp [mul_assoc])⟩
      left_inv := fun k => Subtype.ext (by simp [mul_assoc])
      right_inv := fun k => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun k k' => Subtype.ext (by simp [mul_assoc]) }
  exact D.exists_equiv_coord_eq_iff_of_mulEquiv φ π fun g x => by
    change π ((g : Equiv.Perm X) x) = (π * g * π⁻¹) (π x)
    simp [Equiv.Perm.mul_apply]

end HoltData

theorem eq_of_forall_eq_iff_eq {ι' κ : Type*} [DecidableEq ι'] {Λc : ι' → Type*}
    [∀ i, Nontrivial (Λc i)] {Y : Type*} (e : Y ≃ ∀ i, Λc i) {Ψ : κ → Type*}
    (f : ∀ k, Y → Ψ k) {c : ι' → κ}
    (hcf : ∀ i y y', f (c i) y = f (c i) y' ↔ e y i = e y' i)
    (hconst : ∀ k, k ∉ Set.range c → ∀ y y', f k y = f k y') {i₁ : ι'} {k : κ}
    (hk : ∀ y y', f (c i₁) y = f (c i₁) y' ↔ f k y = f k y') : k = c i₁ := by
  let x₀ : ∀ i, Λc i := fun i => Classical.arbitrary (Λc i)
  have hpair : ∀ i, ∃ y y' : Y, e y i ≠ e y' i ∧ ∀ l, l ≠ i → e y l = e y' l := by
    intro i
    obtain ⟨u, hu⟩ := exists_ne (x₀ i)
    refine ⟨e.symm x₀, e.symm (Function.update x₀ i u), ?_, fun l hl => ?_⟩
    · rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Function.update_self]
      exact hu.symm
    · rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Function.update_of_ne hl]
  by_cases hk' : k ∈ Set.range c
  · obtain ⟨i', rfl⟩ := hk'
    by_contra hne
    have hi' : i' ≠ i₁ := fun h => hne (by rw [h])
    obtain ⟨y, y', hyy', hrest⟩ := hpair i'
    exact hyy' ((hcf i' y y').mp ((hk y y').mp ((hcf i₁ y y').mpr (hrest i₁ hi'.symm))))
  · obtain ⟨y, y', hyy', -⟩ := hpair i₁
    exact absurd ((hcf i₁ y y').mp ((hk y y').mpr (hconst k hk' y y'))) hyy'

end Fibres

section Normalizer

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem toPermHom_mem_normalizer_centralizerImage {V : Subgroup G}
    (n : Subgroup.normalizer (V : Set G)) :
    MulAction.toPermHom (Subgroup.normalizer (V : Set G)) (fixSet Ω V) n ∈
      Subgroup.normalizer (centralizerImage Ω V : Set (Equiv.Perm (fixSet Ω V))) := by
  have key : ∀ n : Subgroup.normalizer (V : Set G), ∀ k ∈ centralizerImage Ω V,
      MulAction.toPermHom _ (fixSet Ω V) n * k * (MulAction.toPermHom _ (fixSet Ω V) n)⁻¹ ∈
        centralizerImage Ω V := by
    intro n k hk
    obtain ⟨c, hc, hck⟩ := mem_centralizerImage.mp hk
    refine mem_centralizerImage.mpr ⟨(n : G) * c * (n : G)⁻¹, ?_, fun ω => ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hv' : (n : G)⁻¹ * v * (n : G) ∈ V := by
        have h := (Subgroup.mem_normalizer_iff.mp n.2 ((n : G)⁻¹ * v * (n : G))).mpr
        exact h (by simpa [mul_assoc] using hv)
      have hcv := Subgroup.mem_centralizer_iff.mp hc _ hv'
      calc v * ((n : G) * c * (n : G)⁻¹)
          = (n : G) * (((n : G)⁻¹ * v * (n : G)) * c) * (n : G)⁻¹ := by group
        _ = (n : G) * (c * ((n : G)⁻¹ * v * (n : G))) * (n : G)⁻¹ := by rw [hcv]
        _ = (n : G) * c * (n : G)⁻¹ * v := by group
    · rw [← map_inv, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, MulAction.toPermHom_apply,
        MulAction.toPermHom_apply, MulAction.toPerm_apply, MulAction.toPerm_apply,
        coe_normalizer_smul, hck, coe_normalizer_smul, mul_smul, mul_smul]
      rfl
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨key n k, fun hk => ?_⟩
  have h := key n⁻¹ _ hk
  rwa [map_inv, inv_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, mul_assoc,
    inv_mul_cancel, mul_one] at h

end Normalizer

section Box

namespace AltConfig

theorem four_le_card_fixSet_of_box (hS : Sec4Setting G Ω) (hαβ : α ≠ β)
    (C : AltConfig G Ω α β) {P : Subgroup G} (hP : IsPGroup 2 P)
    (hP𝒢 : P ≤ stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G (C.γ : Ω) ⊓
      twoPointNormalizer G Ω α β (C.D.L C.i₁))
    {V : Subgroup G} (hV : IsPGroup 2 V) (hV1 : V ≠ ⊥)
    (hVαβ : V ≤ stabilizer G α ⊓ stabilizer G β) (hPV : P ≤ Subgroup.normalizer (V : Set G))
    (Λc : ∀ i, Set (C.D.Ψc i))
    (hbox : ∀ δ : holtDelta G Ω α β, (δ : Ω) ∈ fixSet Ω V ↔ ∀ i, C.D.coord δ i ∈ Λc i)
    (hsize : ∀ i, (Λc i).ncard = 1 ∨ 5 ≤ (Λc i).ncard) (h₁ : 5 ≤ (Λc C.i₁).ncard)
    (hj : ∃ j, j ≠ C.i₁ ∧ 5 ≤ (Λc j).ncard) :
    4 ≤ Nat.card (fixSet Ω P) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set a : fixSet Ω V := ⟨α, mem_fixSet_iff_le_stabilizer.mpr (hVαβ.trans inf_le_left)⟩ with ha
  set b : fixSet Ω V := ⟨β, mem_fixSet_iff_le_stabilizer.mpr (hVαβ.trans inf_le_right)⟩ with hb
  have hab : a ≠ b := fun h => hαβ (congrArg Subtype.val h)
  have h3 := hS.three_le_card_fixSet_of_ne hV hab
  obtain ⟨e, he, hcoord, hreal⟩ := hS.exists_boxEquiv_ccl hαβ C.D C.oddCore_eq_bot C.alt hV
    (a := a) (b := b) rfl rfl Λc hbox (p := fun i => (Λc i).Nontrivial) (fun _ h => h)
    (fun _ h => Set.not_nontrivial_iff.mp h)
  obtain ⟨DK⟩ := hS.holtData_centralizerImage hV hV1 h3
  have hnt : ∀ i, 5 ≤ (Λc i).ncard → (Λc i).Nontrivial := fun i h =>
    Set.one_lt_ncard_iff_nontrivial.mp (by omega)
  have h5 : ∀ j : {i // (Λc i).Nontrivial}, 5 ≤ Fintype.card (Λc j) := fun j => by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    rcases hsize j with h | h
    · exact absurd h (ne_of_gt (Set.one_lt_ncard_iff_nontrivial.mpr j.2))
    · exact h
  obtain ⟨c, hcinj, hca, hcc, -⟩ := DK.ccl (hS.star_centralizerImage hV h3)
    (hS.holtTheorem1Below_centralizerImage hV hV1 h3) hab e h5 hcoord hreal
  set i₁' : {i // (Λc i).Nontrivial} := ⟨C.i₁, hnt _ h₁⟩ with hi₁'
  set k₁ := c i₁' with hk₁
  obtain ⟨-, -, hab₁, hδ₁⟩ := hca i₁'
  have hmem : ∀ δ : holtDelta (centralizerImage Ω V) (fixSet Ω V) a b,
      ((δ : fixSet Ω V) : Ω) ∈ holtDelta G Ω α β := fun δ =>
    (hS.mem_holtDelta_centralizerImage_iff hV h3 hab).mp δ.2
  have hfib₁ : ∀ δ δ' : holtDelta (centralizerImage Ω V) (fixSet Ω V) a b,
      DK.coord (δ : fixSet Ω V) k₁ = DK.coord (δ' : fixSet Ω V) k₁ ↔
        C.D.coord ⟨_, hmem δ⟩ C.i₁ = C.D.coord ⟨_, hmem δ'⟩ C.i₁ := fun δ δ' => by
    rw [(hδ₁ δ δ').1, Subtype.ext_iff, he δ ⟨_, hmem δ⟩ rfl i₁', he δ' ⟨_, hmem δ'⟩ rfl i₁']
  have hPN : ∀ g ∈ P, g ∈ twoPointNormalizer G Ω α β (C.D.L C.i₁) := fun g hg =>
    (Subgroup.mem_inf.mp (hP𝒢 hg)).2
  have hPαβ : ∀ g ∈ P, g • α = α ∧ g • β = β := fun g hg => by
    have h := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (hP𝒢 hg)).1).1
    exact ⟨mem_stabilizer_iff.mp (Subgroup.mem_inf.mp h).1,
      mem_stabilizer_iff.mp (Subgroup.mem_inf.mp h).2⟩
  have hPΔ : ∀ g ∈ P, ∀ ω ∈ holtDelta G Ω α β, g • ω ∈ holtDelta G Ω α β := fun g hg ω hω => by
    have h := mem_stabilizer_iff.mp
      (stabilizer_pair_le α β (twoPointNormalizer_le_stabilizer_pair _ (hPN g hg)))
    rw [← h]
    exact Set.smul_mem_smul_set hω
  have hPK : ∀ g (hg : g ∈ P) (δ : holtDelta (centralizerImage Ω V) (fixSet Ω V) a b),
      ((⟨g, hPV hg⟩ : Subgroup.normalizer (V : Set G)) • (δ : fixSet Ω V)) ∈
        holtDelta (centralizerImage Ω V) (fixSet Ω V) a b := fun g hg δ =>
    (hS.mem_holtDelta_centralizerImage_iff hV h3 hab).mpr (hPΔ g hg _ (hmem δ))
  have hσfix : ∀ g (hg : g ∈ P) (σ : DK.ι ≃ DK.ι), (∀ i y z, DK.coord y i = DK.coord z i ↔
      DK.coord ((⟨g, hPV hg⟩ : Subgroup.normalizer (V : Set G)) • y) (σ i) =
        DK.coord ((⟨g, hPV hg⟩ : Subgroup.normalizer (V : Set G)) • z) (σ i)) → σ k₁ = k₁ := by
    intro g hg σ hσ
    obtain ⟨hg2, hgN⟩ := mem_twoPointNormalizer.mp (hPN g hg)
    have hclaim : ∀ η η' : holtDelta (centralizerImage Ω V) (fixSet Ω V) a b,
        DK.coord (η : fixSet Ω V) k₁ = DK.coord (η' : fixSet Ω V) k₁ ↔
          DK.coord (η : fixSet Ω V) (σ k₁) = DK.coord (η' : fixSet Ω V) (σ k₁) := by
      intro η η'
      set θ : holtDelta (centralizerImage Ω V) (fixSet Ω V) a b := ⟨_, hPK _ (inv_mem hg) η⟩
      set θ' : holtDelta (centralizerImage Ω V) (fixSet Ω V) a b := ⟨_, hPK _ (inv_mem hg) η'⟩
      have hθ : ∀ (ζ : holtDelta (centralizerImage Ω V) (fixSet Ω V) a b),
          (⟨g, hPV hg⟩ : Subgroup.normalizer (V : Set G)) •
            ((⟨_, hPK _ (inv_mem hg) ζ⟩ : holtDelta (centralizerImage Ω V) (fixSet Ω V) a b) :
              fixSet Ω V) = ζ := fun ζ =>
        Subtype.ext (smul_inv_smul g ((ζ : fixSet Ω V) : Ω))
      have hĝ : ∀ (ζ : holtDelta (centralizerImage Ω V) (fixSet Ω V) a b),
          (⟨twoPointHom G Ω α β ⟨g, hg2⟩, twoPointHom_mem_twoPointSection _⟩ :
            twoPointSection G Ω α β) • (⟨_, hmem ⟨_, hPK _ (inv_mem hg) ζ⟩⟩ :
              holtDelta G Ω α β) = ⟨_, hmem ζ⟩ := fun ζ =>
        Subtype.ext (smul_inv_smul g ((ζ : fixSet Ω V) : Ω))
      have h1 := (hσ k₁ θ θ').symm
      rw [hθ η, hθ η'] at h1
      rw [h1, hfib₁ θ θ', hfib₁ η η', ← hĝ η, ← hĝ η']
      exact (C.D.normalizer_L_preserves_fibres hgN _ _).1
    have : ∀ j : {i // (Λc i).Nontrivial}, Nontrivial ↥(Λc j) := fun j =>
      Set.nontrivial_coe_sort.mpr j.2
    exact eq_of_forall_eq_iff_eq e
      (fun k (y : holtDelta (centralizerImage Ω V) (fixSet Ω V) a b) =>
        DK.coord (y : fixSet Ω V) k) (fun i y y' => ((hca i).2.2.2 y y').1)
      (fun k hk y y' => (hcc k hk y).1.trans (hcc k hk y').1.symm) hclaim
  obtain ⟨x', hx'⟩ := DK.coord_surjective (Function.update (DK.coord a) k₁ (DK.coord b k₁))
  have hx'k₁ : DK.coord x' k₁ = DK.coord b k₁ := by rw [hx', Function.update_self]
  have hx'ne : ∀ i, i ≠ k₁ → DK.coord x' i = DK.coord a i := fun i hi => by
    rw [hx', Function.update_of_ne hi]
  have hPx' : ∀ g (hg : g ∈ P),
      DK.coord ((⟨g, hPV hg⟩ : Subgroup.normalizer (V : Set G)) • x') = DK.coord x' ∧
        ∀ y z : fixSet Ω V, DK.coord y = DK.coord z ↔
          DK.coord ((⟨g, hPV hg⟩ : Subgroup.normalizer (V : Set G)) • y) =
            DK.coord ((⟨g, hPV hg⟩ : Subgroup.normalizer (V : Set G)) • z) := by
    intro g hg
    obtain ⟨σ, hσ⟩ := DK.exists_equiv_coord_eq_iff_of_mem_normalizer
      (toPermHom_mem_normalizer_centralizerImage (Ω := Ω) ⟨g, hPV hg⟩)
    replace hσ : ∀ i y z, DK.coord y i = DK.coord z i ↔
        DK.coord ((⟨g, hPV hg⟩ : Subgroup.normalizer (V : Set G)) • y) (σ i) =
          DK.coord ((⟨g, hPV hg⟩ : Subgroup.normalizer (V : Set G)) • z) (σ i) := hσ
    have hσk := hσfix g hg σ hσ
    have hna : (⟨g, hPV hg⟩ : Subgroup.normalizer (V : Set G)) • a = a :=
      Subtype.ext (hPαβ g hg).1
    have hnb : (⟨g, hPV hg⟩ : Subgroup.normalizer (V : Set G)) • b = b :=
      Subtype.ext (hPαβ g hg).2
    refine ⟨funext fun i' => ?_, fun y z => ?_⟩
    · obtain ⟨i, rfl⟩ := σ.surjective i'
      by_cases hi : i = k₁
      · have h := (hσ k₁ x' b).mp hx'k₁
        rw [hi, hσk]
        rw [hσk, hnb] at h
        exact h.trans hx'k₁.symm
      · have h := (hσ i x' a).mp (hx'ne i hi)
        rw [hna] at h
        have hσi : σ i ≠ k₁ := fun h' => hi (σ.injective (h'.trans hσk.symm))
        exact h.trans (hx'ne _ hσi).symm
    · rw [funext_iff, funext_iff]
      constructor
      · intro h i'
        obtain ⟨i, rfl⟩ := σ.surjective i'
        exact (hσ i y z).mp (h i)
      · intro h i
        exact (hσ i y z).mpr (h (σ i))
  set B : Set Ω := {ω | ∃ h : ω ∈ fixSet Ω V, DK.coord ⟨ω, h⟩ = DK.coord x'} with hB
  have hPB : P ≤ stabilizer G B := by
    intro g hg
    rw [mem_stabilizer_set]
    intro ω
    obtain ⟨hx'fix, hcoordeq⟩ := hPx' g hg
    constructor
    · rintro ⟨h, hω⟩
      have hω' : ω ∈ fixSet Ω V := by
        have h' := smul_mem_fixSet_of_mem_normalizer (inv_mem (hPV hg)) h
        rwa [inv_smul_smul] at h'
      refine ⟨hω', ?_⟩
      rw [hcoordeq, hx'fix]
      exact hω
    · rintro ⟨h, hω⟩
      refine ⟨smul_mem_fixSet_of_mem_normalizer (hPV hg) h, ?_⟩
      have h' := (hcoordeq _ _).mp hω
      rw [hx'fix] at h'
      exact h'
  have hBorb : B = Subtype.val '' orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V)) x' := by
    ext ω
    constructor
    · rintro ⟨h, hω⟩
      exact ⟨⟨ω, h⟩, (DK.coord_eq_iff x' ⟨ω, h⟩).mp hω.symm, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, ((DK.coord_eq_iff x' y).mpr hy).symm⟩
  have hBodd : Odd (Nat.card B) := by
    rw [hBorb, Nat.card_image_of_injective Subtype.val_injective]
    exact odd_card_orbit_jOddCore x'
  have hFB : Odd (Nat.card ↥(fixSet Ω P ∩ B)) := by
    rw [Nat.odd_iff] at hBodd ⊢
    rw [← card_modEq_card_fixSet_inter_of_le_stabilizer hP hPB, hBodd]
  obtain ⟨ω₀, hω₀P, hω₀V, hω₀⟩ : (fixSet Ω P ∩ B).Nonempty := by
    have h := hFB.pos
    rw [Nat.card_pos_iff] at h
    exact Set.nonempty_coe_sort.mp h.1
  obtain ⟨j, hj1, hj5⟩ := hj
  set j' : {i // (Λc i).Nontrivial} := ⟨j, hnt _ hj5⟩ with hj'
  have hjk : c j' ≠ k₁ := fun h => hj1 (congrArg Subtype.val (hcinj h))
  obtain ⟨-, -, habj, -⟩ := hca j'
  have hω₀a : ω₀ ≠ α := fun h => by
    have h' : (⟨ω₀, hω₀V⟩ : fixSet Ω V) = a := Subtype.ext h
    rw [h'] at hω₀
    exact hab₁ ((congrFun hω₀ k₁).trans hx'k₁)
  have hω₀b : ω₀ ≠ β := fun h => by
    have h' : (⟨ω₀, hω₀V⟩ : fixSet Ω V) = b := Subtype.ext h
    rw [h'] at hω₀
    exact habj ((congrFun hω₀ (c j')).trans (hx'ne _ hjk)).symm
  have hω₀γ : ω₀ ≠ (C.γ : Ω) := fun h => by
    have hγK : (⟨ω₀, hω₀V⟩ : fixSet Ω V) ∈ holtDelta (centralizerImage Ω V) (fixSet Ω V) a b :=
      (hS.mem_holtDelta_centralizerImage_iff hV h3 hab).mpr
        (show ω₀ ∈ holtDelta G Ω α β by rw [h]; exact C.γ.2)
    exact (hδ₁ ⟨_, hγK⟩ ⟨_, hγK⟩).2.2 ((congrFun hω₀ k₁).trans hx'k₁)
  have hnot : ω₀ ∉ ({α, β, (C.γ : Ω)} : Set Ω) := by
    rintro (h | h | h)
    exacts [hω₀a h, hω₀b h, hω₀γ h]
  have h4 : (insert ω₀ ({α, β, (C.γ : Ω)} : Set Ω)).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem hnot (Set.toFinite _), C.ncard_triple hαβ]
  rw [Nat.card_coe_set_eq, ← h4]
  exact Set.ncard_le_ncard (Set.insert_subset hω₀P (triple_subset_fixSet
    (hP𝒢.trans inf_le_left))) (Set.toFinite _)

theorem false_of_box (hS : Sec4Setting G Ω) (hαβ : α ≠ β) (C : AltConfig G Ω α β)
    {V : Subgroup G} (hV : IsPGroup 2 V) (hV1 : V ≠ ⊥)
    (hVαβ : V ≤ stabilizer G α ⊓ stabilizer G β)
    (hPV : C.S ⊓ twoPointNormalizer G Ω α β (C.D.L C.i₁) ≤ Subgroup.normalizer (V : Set G))
    (Λc : ∀ i, Set (C.D.Ψc i))
    (hbox : ∀ δ : holtDelta G Ω α β, (δ : Ω) ∈ fixSet Ω V ↔ ∀ i, C.D.coord δ i ∈ Λc i)
    (hsize : ∀ i, (Λc i).ncard = 1 ∨ 5 ≤ (Λc i).ncard) (h₁ : 5 ≤ (Λc C.i₁).ncard)
    (hj : ∃ j, j ≠ C.i₁ ∧ 5 ≤ (Λc j).ncard) : False := by
  have h := C.four_le_card_fixSet_of_box hS hαβ (C.sylow.2.1.to_le inf_le_left)
    (inf_le_inf_right _ C.sylow.1) hV hV1 hVαβ hPV Λc hbox hsize h₁ hj
  rw [C.fix_three] at h
  omega

theorem card_ι_eq_one_of_ne_bot (hS : Sec4Setting G Ω) (hαβ : α ≠ β)
    (C : AltConfig G Ω α β) (hT : ¬ Odd (Nat.card (twoPointKernel G Ω α β))) :
    Fintype.card C.D.ι = 1 := by
  by_contra hne
  obtain ⟨j, hj⟩ : ∃ j, j ≠ C.i₁ := by
    by_contra h
    exact hne (Fintype.card_eq_one_iff.mpr
      ⟨C.i₁, fun y => Classical.byContradiction fun hy => h ⟨y, hy⟩⟩)
  set T := C.S ⊓ twoPointKernel G Ω α β with hTdef
  have hT1 : T ≠ ⊥ := fun h => hT ((inf_twoPointKernel_eq_bot_iff C.γ.2 C.sylow).mp h)
  have hSαβ : ∀ x ∈ C.S, x ∈ stabilizer G α ⊓ stabilizer G β := fun x hx =>
    (Subgroup.mem_inf.mp (C.sylow.1 hx)).1
  have hST : ∀ g ∈ C.S, g ∈ Subgroup.normalizer (T : Set G) := fun g hg => by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨hhS, hhK⟩ := Subgroup.mem_inf.mp hh
      exact Subgroup.mem_inf.mpr ⟨C.S.mul_mem (C.S.mul_mem hg hhS) (C.S.inv_mem hg),
        conj_mem_twoPointKernel (hSαβ g hg) hhK⟩
    · intro hh
      obtain ⟨hhS, hhK⟩ := Subgroup.mem_inf.mp hh
      have he : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
      have h1 := conj_mem_twoPointKernel (hSαβ _ (C.S.inv_mem hg)) hhK
      have h2 := C.S.mul_mem (C.S.mul_mem (C.S.inv_mem hg) hhS) (C.S.inv_mem (C.S.inv_mem hg))
      rw [he] at h1 h2
      exact Subgroup.mem_inf.mpr ⟨h2, h1⟩
  have h5 : ∀ i, 5 ≤ (Set.univ : Set (C.D.Ψc i)).ncard := fun i => by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card]
    exact C.D.five_le_card i
  exact C.false_of_box hS hαβ (C.sylow.2.1.to_le inf_le_left) hT1
    (inf_le_right.trans twoPointKernel_le_inf) (fun g hg => hST g (Subgroup.mem_inf.mp hg).1)
    (fun _ => Set.univ)
    (fun δ => iff_of_true (mem_fixSet_iff_le_stabilizer.mpr
      ((inf_le_right.trans (twoPointKernel_le_of_mem δ.2)).trans inf_le_right))
      fun _ => Set.mem_univ _)
    (fun i => Or.inr (h5 i)) (h5 C.i₁) ⟨j, hj, h5 j⟩

end AltConfig

end Box

end CFSG.Holt.H78
