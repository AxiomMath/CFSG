module

public import CFSG.ClassicalInvolution.AschTight.Sec7L98J

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Elementary

variable {G : Type} [Group G]

theorem late_natCard_conjSubE (n : G) (A : Subgroup G) :
    Nat.card ↥(conjSub n A) = Nat.card ↥A :=
  Subgroup.card_map_of_injective (MulAut.conj n).injective

theorem late_conjSub_infE (n : G) (A B : Subgroup G) :
    conjSub n (A ⊓ B) = conjSub n A ⊓ conjSub n B :=
  Subgroup.map_inf_eq A B (MulAut.conj n).toMonoidHom (MulAut.conj n).injective

theorem late_conjSub_supE (n : G) (A B : Subgroup G) :
    conjSub n (A ⊔ B) = conjSub n A ⊔ conjSub n B :=
  Subgroup.map_sup _ _ _

theorem late_mem_normalizer_infE {A B : Subgroup G} {n : G}
    (hA : n ∈ Subgroup.normalizer (A : Set G)) (hB : n ∈ Subgroup.normalizer (B : Set G)) :
    n ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_conjSub_eq] at hA hB ⊢
  rw [late_conjSub_infE, hA, hB]

theorem late_mem_normalizer_supE {A B : Subgroup G} {n : G}
    (hA : n ∈ Subgroup.normalizer (A : Set G)) (hB : n ∈ Subgroup.normalizer (B : Set G)) :
    n ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_conjSub_eq] at hA hB ⊢
  rw [late_conjSub_supE, hA, hB]

theorem late_conjSub_eq_of_leE {A B : Subgroup G} [Finite G] {n : G} (h : conjSub n A ≤ B)
    (hc : Nat.card ↥B ≤ Nat.card ↥A) : conjSub n A = B :=
  Subgroup.eq_of_le_of_card_ge h (by rw [late_natCard_conjSubE]; exact hc)

theorem late_le_normalizer_of_comm_leE {A K : Subgroup G} (h : ⁅A, K⁆ ≤ K) :
    A ≤ Subgroup.normalizer (K : Set G) := by
  intro v hv
  rw [Subgroup.mem_normalizer_iff]
  intro k
  have e : ∀ a k : G, a * k * a⁻¹ = ⁅a, k⁆ * k := fun a k => by
    rw [commutatorElement_def]; group
  constructor
  · intro hk
    rw [e]
    exact K.mul_mem (h (Subgroup.commutator_mem_commutator hv hk)) hk
  · intro hk
    have h1 : v⁻¹ * (v * k * v⁻¹) * v = k := by group
    have h2 := e v⁻¹ (v * k * v⁻¹)
    rw [inv_inv] at h2
    have h3 : ⁅v⁻¹, v * k * v⁻¹⁆ ∈ K := h (Subgroup.commutator_mem_commutator (A.inv_mem hv) hk)
    rw [h1] at h2
    rw [h2]
    exact K.mul_mem h3 hk

end Elementary

section Std

variable {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

structure Std20F (K K' J : Subgroup G) (S : Sylow 2 G) (R R' W V : Subgroup G) (z t : G) :
    Prop where
  hyp : HypOmegaGen (CoreAssembly.conjClass K)
  late_ne_inv : t ≠ z
  late_mnorm : t ∈ Subgroup.normalizer (K : Set G)
  late_card2 : ∀ {U K₀ R₀ : Subgroup G}, U ∈ USet (CoreAssembly.conjClass K) →
    K₀ ∈ CoreAssembly.conjClass K → IsSylow2In R₀ K₀ → Nat.card ↥R₀ = 2 * Nat.card ↥U
  viol : AViol (CoreAssembly.conjClass K) K J z t
  ne : K' ≠ K
  twins : twinSet (CoreAssembly.conjClass K) K = {K, K'}
  swap : ∃ g ∈ Subgroup.centralizer ({z} : Set G), conjSub g K = K'
  htKK : t ∈ K ⊔ K'
  star : aStar (CoreAssembly.conjClass K) K = CoreAssembly.conjClass K
  hSz : (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G)
  hR : IsSylow2In R K
  hRS : R ≤ (S : Subgroup G)
  hR' : IsSylow2In R' K'
  hR'S : R' ≤ (S : Subgroup G)
  hRG : ∀ T ∈ RSet (CoreAssembly.conjClass K), T ≤ (S : Subgroup G) → T = R ∨ T = R'
  hW : W ∈ WSet (CoreAssembly.conjClass K)
  hWS : W ≤ (S : Subgroup G)
  hWN : (S : Subgroup G) ≤ Subgroup.normalizer (W : Set G)
  hV : V ∈ USet (CoreAssembly.conjClass K)
  hVS : V ≤ (S : Subgroup G)
  hVW : V ≤ W
  htV : t ∈ V

theorem Std20F.late_hΩ (d : Std20F K K' J S R R' W V z t) :
    HypOmegaGen (CoreAssembly.conjClass K) :=
  d.hyp

theorem Std20F.late_mem_K (_d : Std20F K K' J S R R' W V z t) :
    K ∈ CoreAssembly.conjClass K :=
  CoreAssembly.mem_conjClass_self K

theorem Std20F.late_mem_J (d : Std20F K K' J S R R' W V z t) :
    J ∈ CoreAssembly.conjClass K :=
  d.viol.mem

theorem Std20F.late_mem_K' (d : Std20F K K' J S R R' W V z t) :
    K' ∈ CoreAssembly.conjClass K := by
  have h : K' ∈ twinSet (CoreAssembly.conjClass K) K := by rw [d.twins]; exact Or.inr rfl
  exact h.1

theorem Std20F.late_hzK' (d : Std20F K K' J S R R' W V z t) : IsUniqueInvolution K' z := by
  have h : K' ∈ twinSet (CoreAssembly.conjClass K) K := by rw [d.twins]; exact Or.inr rfl
  obtain ⟨-, z', hz'K, hz'K'⟩ := h
  rw [d.viol.hzK.eq hz'K]
  exact hz'K'

theorem Std20F.late_J_ne_K (d : Std20F K K' J S R R' W V z t) : J ≠ K := d.viol.ne

theorem Std20F.late_J_ne_K' (d : Std20F K K' J S R R' W V z t) : J ≠ K' := by
  intro h
  apply d.late_ne_inv
  exact d.viol.hzJ.eq (h ▸ d.late_hzK')

theorem Std20F.late_R_eq (d : Std20F K K' J S R R' W V z t) : R = K ⊓ (S : Subgroup G) := by
  refine (d.hR.eq_of_le (S.isPGroup'.to_le inf_le_right) inf_le_left
    (le_inf d.hR.1 d.hRS)).symm

theorem Std20F.late_R'_eq (d : Std20F K K' J S R R' W V z t) : R' = K' ⊓ (S : Subgroup G) := by
  refine (d.hR'.eq_of_le (S.isPGroup'.to_le inf_le_right) inf_le_left
    (le_inf d.hR'.1 d.hR'S)).symm

theorem Std20F.late_K'_le (d : Std20F K K' J S R R' W V z t) :
    K' ≤ Subgroup.normalizer (K : Set G) :=
  Sec6Gen.le_normalizer_of_twin d.late_hΩ d.late_mem_K' d.late_mem_K d.ne d.late_hzK' d.viol.hzK

theorem Std20F.late_K_le (d : Std20F K K' J S R R' W V z t) :
    K ≤ Subgroup.normalizer (K' : Set G) :=
  Sec6Gen.le_normalizer_of_twin d.late_hΩ d.late_mem_K d.late_mem_K' d.ne.symm d.viol.hzK
    d.late_hzK'

theorem Std20F.late_conj_K (d : Std20F K K' J S R R' W V z t) {g : G}
    (hg : g ∈ Subgroup.centralizer ({z} : Set G)) : conjSub g K = K ∨ conjSub g K = K' := by
  have hgz : g * z * g⁻¹ = z := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp hg
    calc g * z * g⁻¹ = z * g * g⁻¹ := by rw [h]
      _ = z := by group
  have h1 : conjSub g K ∈ twinSet (CoreAssembly.conjClass K) K :=
    ⟨d.hyp.conjInvariant g K d.late_mem_K, z, d.viol.hzK, hgz ▸ d.viol.hzK.conj g⟩
  rw [d.twins] at h1
  exact h1

theorem Std20F.late_conj_K' (d : Std20F K K' J S R R' W V z t) {g : G}
    (hg : g ∈ Subgroup.centralizer ({z} : Set G)) : conjSub g K' = K ∨ conjSub g K' = K' := by
  have hgz : g * z * g⁻¹ = z := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp hg
    calc g * z * g⁻¹ = z * g * g⁻¹ := by rw [h]
      _ = z := by group
  have h1 : conjSub g K' ∈ twinSet (CoreAssembly.conjClass K) K :=
    ⟨d.hyp.conjInvariant g K' d.late_mem_K', z, d.viol.hzK, hgz ▸ d.late_hzK'.conj g⟩
  rw [d.twins] at h1
  exact h1

theorem Std20F.late_conj_iff (d : Std20F K K' J S R R' W V z t) {g : G}
    (hg : g ∈ Subgroup.centralizer ({z} : Set G)) : conjSub g K = K ↔ conjSub g K' = K' := by
  constructor
  · intro h
    rcases d.late_conj_K' hg with h' | h'
    · exact absurd (conjSub_injective g (h'.trans h.symm)) d.ne
    · exact h'
  · intro h
    rcases d.late_conj_K hg with h' | h'
    · exact h'
    · exact absurd (conjSub_injective g (h.trans h'.symm)) d.ne

theorem Std20F.late_cent_le_normalizer_sup (d : Std20F K K' J S R R' W V z t) :
    Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer ((K ⊔ K' : Subgroup G) : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_conjSub_eq, late_conjSub_supE]
  rcases d.late_conj_K hg with h | h
  · rw [h, (d.late_conj_iff hg).mp h]
  · rcases d.late_conj_K' hg with h' | h'
    · rw [h, h', sup_comm]
    · exact absurd (conjSub_injective g (h.trans h'.symm)) d.ne.symm

theorem Std20F.late_S_inf_sup (d : Std20F K K' J S R R' W V z t) :
    (S : Subgroup G) ⊓ (K ⊔ K') = R ⊔ R' := by
  have hRR' : IsSylow2In (R ⊔ R') (K ⊔ K') := by
    have := Sec7.isSylow2In_sup_of_sylow d.late_K'_le d.hR d.hR'
      (fun g hg => by
        rw [d.late_R_eq]
        exact late_mem_normalizer_infE (d.late_K'_le (d.hR'.1 hg))
          (Subgroup.le_normalizer (d.hR'S hg)))
      (fun g hg => by
        rw [d.late_R_eq]
        exact ⟨hg.2, d.hR'S hg.1⟩)
    exact this
  exact hRR'.eq_of_le (S.isPGroup'.to_le inf_le_left) inf_le_right
    (le_inf (sup_le d.hRS d.hR'S) (sup_le (d.hR.1.trans le_sup_left) (d.hR'.1.trans le_sup_right)))

theorem Std20F.late_isSylow2In_RR' (d : Std20F K K' J S R R' W V z t) :
    IsSylow2In (R ⊔ R') (K ⊔ K') :=
  Sec7.isSylow2In_sup_of_sylow d.late_K'_le d.hR d.hR'
    (fun g hg => by
      rw [d.late_R_eq]
      exact late_mem_normalizer_infE (d.late_K'_le (d.hR'.1 hg))
        (Subgroup.le_normalizer (d.hR'S hg)))
    (fun g hg => by
      rw [d.late_R_eq]
      exact ⟨hg.2, d.hR'S hg.1⟩)

theorem Std20F.late_J_not_twin (d : Std20F K K' J S R R' W V z t) :
    J ∉ twinSet (CoreAssembly.conjClass K) K := by
  rintro ⟨-, z', hz', hj'⟩
  exact d.late_ne_inv ((d.viol.hzJ.eq hj').trans (d.viol.hzK.eq hz').symm)

theorem Std20F.late_inA (d : Std20F K K' J S R R' W V z t) :
    InA (CoreAssembly.conjClass K) K J :=
  ⟨d.viol.star, d.viol.not_nbr, z, t, d.viol.hzK, d.viol.hzJ,
    fun ⟨g, hg, he⟩ => d.viol.no_conj g hg he⟩

theorem Std20F.late_JW_data (d : Std20F K K' J S R R' W V z t)
    (hJW : J ⊓ W ∈ USet (CoreAssembly.conjClass K)) :
    IsPGroup 2 ↥(J ⊓ W) ∧ 4 ≤ Nat.card ↥(J ⊓ W) := by
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet d.late_hΩ hJW
  exact ⟨Sec6Gen.isPGroup_of_mem_USet d.late_hΩ hJW, h4⟩

theorem Std20F.late_t_mem_JW (d : Std20F K K' J S R R' W V z t)
    (hJW : J ⊓ W ∈ USet (CoreAssembly.conjClass K)) : t ∈ J ⊓ W := by
  obtain ⟨hP2, h4⟩ := d.late_JW_data hJW
  exact AscL62.mem_of_uniqueInvolution_of_pGroup d.viol.hzJ inf_le_left hP2 (by omega)

theorem Std20F.late_JW_le_N_K (d : Std20F K K' J S R R' W V z t)
    (hJW : J ⊓ W ∈ USet (CoreAssembly.conjClass K)) :
    J ⊓ W ≤ Subgroup.normalizer (K : Set G) := by
  obtain ⟨hP2, h4⟩ := d.late_JW_data hJW
  exact Sec6Gen.le_normalizer_of_le_centralizer d.late_hΩ d.late_mem_K d.late_mem_J
    d.late_J_ne_K.symm d.viol.hzK inf_le_left hP2 (by omega)
    (inf_le_right.trans (d.hWS.trans d.hSz))

theorem Std20F.late_JW_le_N_K' (d : Std20F K K' J S R R' W V z t)
    (hJW : J ⊓ W ∈ USet (CoreAssembly.conjClass K)) :
    J ⊓ W ≤ Subgroup.normalizer (K' : Set G) := by
  obtain ⟨hP2, h4⟩ := d.late_JW_data hJW
  exact Sec6Gen.le_normalizer_of_le_centralizer d.late_hΩ d.late_mem_K' d.late_mem_J
    d.late_J_ne_K'.symm d.late_hzK' inf_le_left hP2 (by omega)
    (inf_le_right.trans (d.hWS.trans d.hSz))

theorem Std20F.late_isSylow2In_JW (d : Std20F K K' J S R R' W V z t)
    (hJW : J ⊓ W ∈ USet (CoreAssembly.conjClass K)) :
    IsSylow2In (J ⊓ W) (J ⊓ Subgroup.centralizer ({z} : Set G)) := by
  obtain ⟨hP2, h4⟩ := d.late_JW_data hJW
  have hle : J ⊓ W ≤ J ⊓ Subgroup.centralizer ({z} : Set G) :=
    inf_le_inf_left J (d.hWS.trans d.hSz)
  have htJW := d.late_t_mem_JW hJW
  obtain ⟨V₀, hV₀, hle'⟩ := IsSylow2In.exists_ge hP2 hle
  have htV₀ : t ∈ V₀ := hle' htJW
  rcases Sec6Gen.l6_2Gen G (CoreAssembly.conjClass K) d.late_hΩ K d.late_mem_K z d.viol.hzK J
    d.late_mem_J d.late_J_not_twin t d.viol.hzJ V₀ hV₀ htV₀ with h | h | h | h
  · exfalso
    exact h.2 (mem_normalizer_iff_conjSub_eq.mp
      d.late_mnorm)
  · exfalso
    have hc := Subgroup.card_le_of_le hle'
    rw [h.1, Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact d.viol.hzJ.sq)
      d.viol.hzJ.ne_one] at hc
    omega
  · have hcard := Sec6Gen.natCard_eq_of_mem_USet d.late_hΩ d.late_mem_J hJW h.1 inf_le_left
      (hV₀.1.trans inf_le_left)
    have heq : J ⊓ W = V₀ := Subgroup.eq_of_le_of_card_ge hle' hcard.ge
    rw [heq]
    exact hV₀
  · exfalso
    have hN : V₀ ≤ Subgroup.normalizer (K : Set G) :=
      late_le_normalizer_of_comm_leE (h.2.trans (oddCoreOf_le_self K))
    exact d.viol.not_nbr ⟨d.late_mem_J, d.late_J_ne_K, V₀, h.1, hV₀.1.trans inf_le_left, hN⟩

theorem Std20F.late_isSylow2In_P (d : Std20F K K' J S R R' W V z t)
    (hJW : J ⊓ W ∈ USet (CoreAssembly.conjClass K)) :
    IsSylow2In (R ⊔ R' ⊔ (J ⊓ W))
      ((K ⊔ K') ⊔ (J ⊓ Subgroup.centralizer ({z} : Set G))) := by
  have hVS : J ⊓ W ≤ (S : Subgroup G) := inf_le_right.trans d.hWS
  refine Sec7.isSylow2In_sup_of_sylow ?_ d.late_isSylow2In_RR' (d.late_isSylow2In_JW hJW) ?_ ?_
  · exact inf_le_right.trans d.late_cent_le_normalizer_sup
  · intro g hg
    have hgS := hVS hg
    have h1 : g ∈ Subgroup.normalizer (R : Set G) := by
      rw [d.late_R_eq]
      exact late_mem_normalizer_infE (d.late_JW_le_N_K hJW hg) (Subgroup.le_normalizer hgS)
    have h2 : g ∈ Subgroup.normalizer (R' : Set G) := by
      rw [d.late_R'_eq]
      exact late_mem_normalizer_infE (d.late_JW_le_N_K' hJW hg) (Subgroup.le_normalizer hgS)
    exact late_mem_normalizer_supE h1 h2
  · rw [← d.late_S_inf_sup]
    exact le_inf (inf_le_left.trans hVS) inf_le_right

theorem Std20F.late_P_le_S (d : Std20F K K' J S R R' W V z t) :
    R ⊔ R' ⊔ (J ⊓ W) ≤ (S : Subgroup G) :=
  sup_le (sup_le d.hRS d.hR'S) (inf_le_right.trans d.hWS)

theorem Std20F.late_P_inv (d : Std20F K K' J S R R' W V z t)
    (hWeq : W = (W ⊓ K) ⊔ (W ⊓ J)) {x : G} (hxS : x ∈ (S : Subgroup G))
    (hxK : conjSub x K = K) :
    conjSub x (R ⊔ R' ⊔ (J ⊓ W)) = R ⊔ R' ⊔ (J ⊓ W) := by
  have hxz : x ∈ Subgroup.centralizer ({z} : Set G) := d.hSz hxS
  have hxK' := (d.late_conj_iff hxz).mp hxK
  have hxS' : conjSub x (S : Subgroup G) = S := conjSub_eq_self_of_mem hxS
  have hxW : conjSub x W = W := mem_normalizer_iff_conjSub_eq.mp (d.hWN hxS)
  have hR : conjSub x R = R := by rw [d.late_R_eq, late_conjSub_infE, hxK, hxS']
  have hR' : conjSub x R' = R' := by rw [d.late_R'_eq, late_conjSub_infE, hxK', hxS']
  have hWP : W ≤ R ⊔ R' ⊔ (J ⊓ W) := by
    conv_lhs => rw [hWeq]
    refine sup_le ?_ ?_
    · have : W ⊓ K ≤ R := by
        rw [d.late_R_eq]
        exact le_inf inf_le_right (inf_le_left.trans d.hWS)
      exact this.trans (le_sup_left.trans le_sup_left)
    · rw [inf_comm]
      exact le_sup_right
  have hle : conjSub x (R ⊔ R' ⊔ (J ⊓ W)) ≤ R ⊔ R' ⊔ (J ⊓ W) := by
    rw [late_conjSub_supE, late_conjSub_supE, hR, hR']
    refine sup_le le_sup_left ?_
    refine le_trans ?_ hWP
    calc conjSub x (J ⊓ W) ≤ conjSub x W := conjSub_mono inf_le_right
      _ = W := hxW
  exact late_conjSub_eq_of_leE hle le_rfl

theorem Std20F.late_98 (d : Std20F K K' J S R R' W V z t)
    (hJW : J ⊓ W ∈ USet (CoreAssembly.conjClass K)) (hWeq : W = (W ⊓ K) ⊔ (W ⊓ J))
    {X : Subgroup G} (hX2 : IsPGroup 2 X) (hXS : X ≤ (S : Subgroup G))
    (hXt : ∀ x ∈ X, x * t = t * x) (hXK : ∀ x ∈ X, conjSub x K = K) :
    ((∀ x ∈ X, conjSub x K = K) ↔ (∀ x ∈ X, conjSub x J = J)) ∧
      ((∀ x ∈ X, ∀ w ∈ W ⊓ K, x * w = w * x) →
        ∃ A : Subgroup G,
          ((W ⊓ J) ⊔ (W ⊓ K)) ⊔ X = ((W ⊓ J) ⊔ (W ⊓ K)) ⊔ A ∧
          ((W ⊓ J) ⊔ (W ⊓ K)) ⊓ A = ⊥ ∧
          (∀ a ∈ A, ∀ y ∈ (W ⊓ J) ⊔ (W ⊓ K), a * y = y * a) ∧
          A ≤ centralizerModOdd ⊤ (K ⊔ K') ∧ A ≤ centralizerModOdd ⊤ J) := by
  have hXc : X ≤ Subgroup.centralizer ({z, t} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rcases hh with rfl | hh
    · have := Subgroup.mem_centralizer_singleton_iff.mp (d.hSz (hXS hx))
      exact this.symm
    · rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (hXt x hx).symm
  have hJS : 2 < Nat.card ↥(J ⊓ (S : Subgroup G)) := by
    obtain ⟨-, h4⟩ := d.late_JW_data hJW
    have := Subgroup.card_le_of_le (inf_le_inf_left J d.hWS : J ⊓ W ≤ J ⊓ (S : Subgroup G))
    omega
  exact Sec7.l9_8GenS G (CoreAssembly.conjClass K) d.late_hΩ K d.late_mem_K J d.late_mem_J
    d.late_inA z t d.viol.hzK d.viol.hzJ K' d.late_mem_K' d.ne d.twins X hX2 hXc
    (R ⊔ R' ⊔ (J ⊓ W)) (d.late_isSylow2In_P hJW)
    (fun x hx => d.late_P_inv hWeq (hXS hx) (hXK x hx)) S
    (sup_le d.late_P_le_S hXS) hJS W d.hW d.hWS

theorem Std20F.late_cfg98 (d : Std20F K K' J S R R' W V z t)
    (hJW : J ⊓ W ∈ USet (CoreAssembly.conjClass K)) :
    Sec7.Cfg98 (CoreAssembly.conjClass K) K J K' ⊥ (R ⊔ R' ⊔ (J ⊓ W)) z t S W := by
  have hJS : 2 < Nat.card ↥(J ⊓ (S : Subgroup G)) := by
    obtain ⟨-, h4⟩ := d.late_JW_data hJW
    have := Subgroup.card_le_of_le (inf_le_inf_left J d.hWS : J ⊓ W ≤ J ⊓ (S : Subgroup G))
    omega
  exact ⟨d.late_hΩ, d.late_mem_K, d.late_mem_J, d.late_inA, d.viol.hzK, d.viol.hzJ,
    d.late_mem_K', d.ne, d.twins, IsPGroup.of_bot, bot_le, d.late_isSylow2In_P hJW,
    fun x hx => by rw [Subgroup.mem_bot.mp hx, conjSub_one],
    by rw [sup_bot_eq]; exact d.late_P_le_S, hJS, d.hW, d.hWS⟩

theorem Std20F.late_tor (d : Std20F K K' J S R R' W V z t)
    (hJW : J ⊓ W ∈ USet (CoreAssembly.conjClass K)) (hWeq : W = (W ⊓ K) ⊔ (W ⊓ J)) :
    ∃ r ∈ R, ∃ r' ∈ R', (∀ x ∈ W, (r * r') * x * (r * r')⁻¹ = x⁻¹) ∧ r * t * r⁻¹ = z * t := by
  have c := d.late_cfg98 hJW
  obtain ⟨u, v, T, hu, hv, tor⟩ := Sec7.Cfg98.exists_tor c Sec6Gen.l6_4ThreeGenAll
  have hR : IsSylow2In (K ⊓ (S : Subgroup G)) K := d.late_R_eq ▸ d.hR
  have hR' : IsSylow2In (K' ⊓ (S : Subgroup G)) K' := d.late_R'_eq ▸ d.hR'
  have hcR := d.late_card2 tor.hU d.late_mem_K hR
  rw [Nat.card_zpowers] at hcR
  obtain ⟨r, hr, hru⟩ : ∃ r ∈ K ⊓ (S : Subgroup G), r ∉ Subgroup.zpowers u := by
    by_contra hcon
    push Not at hcon
    have hle : K ⊓ (S : Subgroup G) ≤ Subgroup.zpowers u := fun x hx => hcon x hx
    have h1 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers] at h1
    have : 0 < orderOf u := by
      rw [← Nat.card_zpowers]; exact Nat.card_pos
    omega
  obtain ⟨u', hu'1, hu'U, -⟩ := tor.hU'
  have hcR' := d.late_card2 hu'U d.late_mem_K' hR'
  obtain ⟨r', hr', hr'c⟩ : ∃ r' ∈ K' ⊓ (S : Subgroup G),
      r' ∉ Subgroup.centralizer ({t} : Set G) := by
    by_contra hcon
    push Not at hcon
    have hle : K' ⊓ (S : Subgroup G) ≤ Subgroup.zpowers u' := by
      rw [hu'1]
      exact le_inf le_rfl (fun x hx => hcon x hx)
    have h1 := Subgroup.card_le_of_le hle
    have : 0 < Nat.card ↥(Subgroup.zpowers u') := Nat.card_pos
    omega
  obtain ⟨hinv, -⟩ := tor.hcent r hr hru r' hr' hr'c
  have hUV : (Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) = W := by
    rw [hu, hv, inf_comm K W, inf_comm J W]
    exact hWeq.symm
  refine ⟨r, d.late_R_eq ▸ hr, r', d.late_R'_eq ▸ hr', fun x hx => hinv x (hUV ▸ hx),
    tor.he1 r hr hru⟩

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
