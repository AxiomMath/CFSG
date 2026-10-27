
module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Base
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Block
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Gen
public import CFSG.Sporadic.J4.Group

@[expose] public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Kc3J4 CFSG.QuasithinUnique.A5.Kc3Gen
  CFSG.Blueprint
open scoped Pointwise commutatorElement

theorem kc3_core_rad {G : Type} [Group G] [Finite G] {K L S₀ T₀ R : Subgroup G}
    (hK5 : ¬ 5 ^ 2 ∣ Nat.card K) (hLK : L ≤ K) (hL : D5Plus L) (hLp : ⁅L, L⁆ = L)
    (hS : IsPGroup 2 S₀) (hT : IsPGroup 2 T₀)
    (hST : S₀ ≤ T₀) (hTK : T₀ ≤ Subgroup.normalizer (K : Set G))
    (hR2 : IsPGroup 2 R) (hRK : R ≤ K) (hLR : L ≤ Subgroup.normalizer (R : Set G))
    (hSR : S₀ ≤ Subgroup.normalizer (R : Set G))
    (hCR : K ⊓ Subgroup.centralizer (R : Set G) ≤ R)
    (hnum : ∃ g ∈ L, orderOf g = 5 ∧
      16 < (R ⊓ Subgroup.centralizer ({g} : Set G)).relIndex R) :
    ∃ X S₁ : Subgroup G, CharTwo X ∧ L ⊔ S₀ ≤ X ∧ X ≤ K ⊔ T₀ ∧ IsSylowTwoOf S₁ X ∧ S₀ ≤ S₁ ∧
      ¬ IsSubnormal L (L ⊔ S₁) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨V, Q, hVQ, hQL, hQ2, hLQ, hLV, hQLV, α, hα, hαQ, β, hβ⟩ := hL
  have hcharTwo : CharTwo ((K ⊔ T₀) ⊓ Subgroup.normalizer (R : Set G)) :=
    charTwo_normalizer hT hTK hR2 hRK hCR
  set X : Subgroup G := (K ⊔ T₀) ⊓ Subgroup.normalizer (R : Set G) with hX
  have hLSX : L ⊔ S₀ ≤ X :=
    sup_le (le_inf (hLK.trans le_sup_left) hLR) (le_inf (hST.trans le_sup_right) hSR)
  have hRX : R ≤ X := le_inf (hRK.trans le_sup_left) Subgroup.le_normalizer
  obtain ⟨S₁, hSS₁, hS₁⟩ := exists_sylowTwoOf_le (le_sup_right.trans hLSX) hS
  refine ⟨X, S₁, hcharTwo, hLSX, inf_le_left, hS₁, hSS₁, ?_⟩
  intro hsub
  have hL25 : ¬ 5 ^ 2 ∣ Nat.card L := fun h => hK5 (h.trans (Subgroup.card_dvd_of_le hLK))
  have hLS₁ : L ⊔ S₁ ≤ K ⊔ T₀ := sup_le (hLK.trans le_sup_left) (hS₁.1.trans inf_le_left)
  have hY : ¬ 5 ^ 2 ∣ Nat.card ↥(L ⊔ S₁) :=
    not_prime_sq_dvd_of_le_sup (p := 5) (by norm_num) hT hTK hLS₁ hK5
  have hgen : ∀ N' : Subgroup G, (∀ x ∈ L, orderOf x = 5 → x ∈ N') → L ≤ N' := fun N' h =>
    le_of_five_elements hQ2 hQL α hα hαQ hLp h
  have hnorm := normalizes_of_isSubnormal (p := 5) hsub (five_dvd_card α hα) hY hgen
  have hS₁L : S₁ ≤ Subgroup.normalizer (L : Set G) := le_sup_right.trans hnorm
  have hRS₁ : R ≤ S₁ := le_of_normalizes_isSylowTwoOf hS₁ hRX inf_le_right hR2
  have hRL : R ≤ Subgroup.normalizer (L : Set G) := hRS₁.trans hS₁L
  obtain ⟨g, hgL, hg5, hg16⟩ := hnum
  have hmax : ∀ D' : Subgroup G, D' ≤ L → L ≤ Subgroup.normalizer (D' : Set G) →
      IsPGroup 2 D' → D' ≤ Q := fun D' h1 h2 h3 => le_Q_of_normal_two α hα hαQ h1 h2 h3
  have h1 := relIndex_centralizer_le hgL hg5 hL25 hQL hLQ hQ2 hmax hQLV hR2 hRL hLR
  have hV : Nat.card V = 16 := card_V β
  omega

@[expose] def blockRadAbs {X : Type*} [Group X] (L : Subgroup X) : Subgroup X :=
  pCoreOf 2 (Subgroup.normalizer ((pCoreOf 2 L : Subgroup X) : Set X))

theorem normalizer_map_equiv_eq {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (S : Subgroup X) :
    Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup Y) : Set Y) =
      (Subgroup.normalizer (S : Set X)).map e.toMonoidHom := by
  apply le_antisymm
  · intro y hy
    refine ⟨e.symm y, ?_, by simp⟩
    change e.symm y ∈ Subgroup.normalizer (S : Set X)
    rw [Subgroup.mem_normalizer_iff] at hy ⊢
    intro h
    have h1 := hy (e h)
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv] at h1
    simpa only [MulEquiv.symm_apply_apply, map_mul, map_inv] using h1
  · exact Subgroup.le_normalizer_map e.toMonoidHom

theorem blockRadAbs_map_equiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (L : Subgroup X) :
    blockRadAbs (L.map e.toMonoidHom) = (blockRadAbs L).map e.toMonoidHom := by
  unfold blockRadAbs
  rw [CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 e L, normalizer_map_equiv_eq,
    CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 e]

theorem le_normalizer_blockRadAbs {X : Type*} [Group X] (L : Subgroup X) :
    L ≤ Subgroup.normalizer (blockRadAbs L : Set X) := by
  have h1 : L ≤ Subgroup.normalizer ((pCoreOf 2 L : Subgroup X) : Set X) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  exact h1.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)

theorem isPGroup_blockRadAbs {X : Type*} [Group X] [Finite X] (L : Subgroup X) :
    IsPGroup 2 (blockRadAbs L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _

@[expose] def blockRadIn {G : Type} [Group G] (K L : Subgroup G) : Subgroup G :=
  (blockRadAbs (L.subgroupOf K)).map K.subtype

theorem isPGroup_blockRadIn {G : Type} [Group G] [Finite G] (K L : Subgroup G) :
    IsPGroup 2 (blockRadIn K L) :=
  (isPGroup_blockRadAbs _).map K.subtype

theorem blockRadIn_le {G : Type} [Group G] (K L : Subgroup G) : blockRadIn K L ≤ K :=
  Subgroup.map_subtype_le _

theorem le_normalizer_blockRadIn {G : Type} [Group G] {K L : Subgroup G} (hLK : L ≤ K) :
    L ≤ Subgroup.normalizer (blockRadIn K L : Set G) := by
  apply le_normalizer_of_conj_mem
  intro l hl r hr
  obtain ⟨r', hr', rfl⟩ := hr
  have hl' : (⟨l, hLK hl⟩ : ↥K) ∈ L.subgroupOf K := hl
  have hN := le_normalizer_blockRadAbs (L.subgroupOf K) hl'
  have := (Subgroup.mem_normalizer_iff.1 hN r').1 hr'
  exact ⟨_, this, rfl⟩

theorem normalizer_blockRadIn {G : Type} [Group G] {K L : Subgroup G} {s : G}
    (hsK : s ∈ Subgroup.normalizer (K : Set G)) (hsL : s ∈ Subgroup.normalizer (L : Set G)) :
    s ∈ Subgroup.normalizer (blockRadIn K L : Set G) := by
  have fwd : ∀ s : G, s ∈ Subgroup.normalizer (K : Set G) → s ∈ Subgroup.normalizer (L : Set G) →
      ∀ r ∈ blockRadIn K L, s * r * s⁻¹ ∈ blockRadIn K L := by
    intro s hsK hsL r hr
    obtain ⟨r', hr', rfl⟩ := hr
    let φ : ↥K ≃* ↥K := K.normalizerMonoidHom ⟨s, hsK⟩
    have hφ : ∀ x : ↥K, ((φ x : ↥K) : G) = s * (x : G) * s⁻¹ := fun x =>
      K.normalizerMonoidHom_apply_apply_coe ⟨s, hsK⟩ x
    have hL : (L.subgroupOf K).map φ.toMonoidHom = L.subgroupOf K := by
      apply le_antisymm
      · rintro _ ⟨y, hy, rfl⟩
        have hy' : (y : G) ∈ L := hy
        have := (Subgroup.mem_normalizer_iff.1 hsL (y : G)).1 hy'
        show ((φ y : ↥K) : G) ∈ L
        rw [hφ]
        exact this
      · intro x hx
        refine ⟨φ.symm x, ?_, by simp⟩
        have hx' : (x : G) ∈ L := hx
        have h2 : ((φ (φ.symm x) : ↥K) : G) = (x : G) := by simp
        rw [hφ] at h2
        have h3 : s * ((φ.symm x : ↥K) : G) * s⁻¹ ∈ L := by rw [h2]; exact hx'
        have := (Subgroup.mem_normalizer_iff.1 hsL ((φ.symm x : ↥K) : G)).2 h3
        exact this
    have h1 := blockRadAbs_map_equiv φ (L.subgroupOf K)
    rw [hL] at h1
    have h2 : φ r' ∈ blockRadAbs (L.subgroupOf K) := by
      rw [h1]
      exact ⟨r', hr', rfl⟩
    exact ⟨φ r', h2, hφ r'⟩
  rw [Subgroup.mem_normalizer_iff]
  intro r
  refine ⟨fwd s hsK hsL r, fun hr => ?_⟩
  have hsK' : s⁻¹ ∈ Subgroup.normalizer (K : Set G) := inv_mem hsK
  have hsL' : s⁻¹ ∈ Subgroup.normalizer (L : Set G) := inv_mem hsL
  have := fwd s⁻¹ hsK' hsL' _ hr
  simpa [mul_assoc] using this

@[expose] def BlockRadAbs (X : Type) [Group X] : Prop :=
  ∀ L : Subgroup X, D5Plus L → ⁅L, L⁆ = L →
    (¬ ∃ y : X, orderOf y = 2 ∧ ∀ l ∈ L, l * y = y * l) →
    Subgroup.centralizer (blockRadAbs L : Set X) ≤ blockRadAbs L ∧
      ∃ g ∈ L, orderOf g = 5 ∧
        16 < (blockRadAbs L ⊓ Subgroup.centralizer ({g} : Set X)).relIndex (blockRadAbs L)

theorem blockRadAbs_of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : BlockRadAbs X) : BlockRadAbs Y := by
  intro L hL hLp hno
  set L' : Subgroup X := L.map e.symm.toMonoidHom with hL'
  have hL'D : D5Plus L' := d5Plus_map e.symm.toMonoidHom e.symm.injective hL
  have hL'p : ⁅L', L'⁆ = L' := by
    rw [hL', ← Subgroup.map_commutator, hLp]
  have hno' : ¬ ∃ y : X, orderOf y = 2 ∧ ∀ l ∈ L', l * y = y * l := by
    rintro ⟨y, hyo, hyc⟩
    apply hno
    refine ⟨e y, by rw [e.orderOf_eq]; exact hyo, fun l hl => ?_⟩
    have := hyc (e.symm l) ⟨l, hl, rfl⟩
    have h2 := congrArg e this
    simpa using h2
  obtain ⟨hC, g, hgL, hg5, hg16⟩ := h L' hL'D hL'p hno'
  have hLL : L'.map e.toMonoidHom = L := by
    rw [hL', Subgroup.map_map]
    have : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id Y := by
      ext y
      simp
    rw [this, Subgroup.map_id]
  have hR : blockRadAbs L = (blockRadAbs L').map e.toMonoidHom := by
    have := blockRadAbs_map_equiv e L'
    rw [hLL] at this
    exact this
  have hf : Function.Injective e.toMonoidHom := e.injective
  rw [hR]
  refine ⟨?_, e g, by rw [← hLL]; exact ⟨g, hgL, rfl⟩, by rw [e.orderOf_eq]; exact hg5, ?_⟩
  · intro y hy
    have hy' : e.symm y ∈ Subgroup.centralizer (blockRadAbs L' : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      have := Subgroup.mem_centralizer_iff.1 hy (e r) ⟨r, hr, rfl⟩
      apply e.injective
      simpa using this
    exact ⟨e.symm y, hC hy', by simp⟩
  · have heq : (blockRadAbs L').map e.toMonoidHom ⊓ Subgroup.centralizer ({e g} : Set Y) =
        ((blockRadAbs L') ⊓ Subgroup.centralizer ({g} : Set X)).map e.toMonoidHom := by
      ext x
      rw [Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_map]
      constructor
      · rintro ⟨⟨n, hn, rfl⟩, hxc⟩
        refine ⟨n, Subgroup.mem_inf.2 ⟨hn, ?_⟩, rfl⟩
        have h1 := Subgroup.mem_centralizer_singleton_iff.1 hxc
        refine Subgroup.mem_centralizer_singleton_iff.2 ?_
        apply e.injective
        simpa using h1
      · rintro ⟨n, hn, rfl⟩
        obtain ⟨hn1, hn2⟩ := Subgroup.mem_inf.1 hn
        refine ⟨⟨n, hn1, rfl⟩, ?_⟩
        have h1 := Subgroup.mem_centralizer_singleton_iff.1 hn2
        refine Subgroup.mem_centralizer_singleton_iff.2 ?_
        simpa using congrArg e h1
    rw [heq, Subgroup.relIndex_map_map_of_injective _ _ hf]
    exact hg16

theorem blockRadIn_conditions {G : Type} [Group G] [Finite G] {K L : Subgroup G} (hLK : L ≤ K)
    (hL : D5Plus L) (hLp : ⁅L, L⁆ = L)
    (hno : ¬ ∃ y ∈ K, orderOf y = 2 ∧ ∀ l ∈ L, l * y = y * l) (hB : BlockRadAbs ↥K) :
    K ⊓ Subgroup.centralizer (blockRadIn K L : Set G) ≤ blockRadIn K L ∧
      ∃ g ∈ L, orderOf g = 5 ∧
        16 < (blockRadIn K L ⊓ Subgroup.centralizer ({g} : Set G)).relIndex (blockRadIn K L) := by
  have hL' : D5Plus (L.subgroupOf K) := d5Plus_subgroupOf hLK hL
  have hLp' : ⁅L.subgroupOf K, L.subgroupOf K⁆ = L.subgroupOf K := by
    rw [commutator_subgroupOf_self hLK, hLp]
  have hno' : ¬ ∃ y : ↥K, orderOf y = 2 ∧ ∀ l ∈ L.subgroupOf K, l * y = y * l := by
    rintro ⟨y, hyo, hyc⟩
    apply hno
    refine ⟨(y : G), y.2, by rw [Subgroup.orderOf_coe]; exact hyo, fun l hl => ?_⟩
    have := hyc ⟨l, hLK hl⟩ hl
    exact congrArg Subtype.val this
  obtain ⟨hC, g, hgL, hg5, hg16⟩ := hB _ hL' hLp' hno'
  have hf : Function.Injective K.subtype := K.subtype_injective
  refine ⟨?_, (g : G), hgL, by rw [Subgroup.orderOf_coe]; exact hg5, ?_⟩
  · rintro c ⟨hcK, hcR⟩
    have hc' : (⟨c, hcK⟩ : ↥K) ∈ Subgroup.centralizer (blockRadAbs (L.subgroupOf K) : Set ↥K) := by
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      have := Subgroup.mem_centralizer_iff.1 hcR (r : G) ⟨r, hr, rfl⟩
      exact Subtype.ext this
    exact ⟨_, hC hc', rfl⟩
  · have heq : blockRadIn K L ⊓ Subgroup.centralizer ({(g : G)} : Set G) =
        (blockRadAbs (L.subgroupOf K) ⊓ Subgroup.centralizer ({g} : Set ↥K)).map K.subtype := by
      ext x
      rw [Subgroup.mem_inf, Subgroup.mem_map]
      constructor
      · rintro ⟨⟨n, hn, rfl⟩, hxc⟩
        refine ⟨n, Subgroup.mem_inf.2 ⟨hn, ?_⟩, rfl⟩
        have h1 := Subgroup.mem_centralizer_singleton_iff.1 hxc
        exact Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext h1)
      · rintro ⟨n, hn, rfl⟩
        obtain ⟨hn1, hn2⟩ := Subgroup.mem_inf.1 hn
        refine ⟨⟨n, hn1, rfl⟩, ?_⟩
        have h1 := Subgroup.mem_centralizer_singleton_iff.1 hn2
        exact Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val h1)
    rw [heq]
    unfold blockRadIn
    rw [Subgroup.relIndex_map_map_of_injective _ _ hf]
    exact hg16

@[expose] def J4BlockRad : Prop := BlockRadAbs ↥CFSG.Sporadic.J4.J

end CFSG.QuasithinUnique.A5
