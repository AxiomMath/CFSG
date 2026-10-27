module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitHypothesisISupport
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalSixConj
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalSixTools

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaLocal.Five

open SectionSix SectionSix.BarTools

section Abstract

variable {X : Type} [Group X]

theorem isPGroup_zpowers_of_pow {x : X} {n : ℕ} (hx : x ^ (2 ^ n) = 1) :
    IsPGroup 2 (Subgroup.zpowers x) := by
  rintro ⟨y, hy⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  refine ⟨n, Subtype.ext ?_⟩
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

theorem sup_inf_eq_of_le {Y E A : Subgroup X} (hYA : Y ≤ A)
    (hEY : E ≤ Subgroup.normalizer (Y : Set X)) (hEA : E ⊓ A = ⊥) : (Y ⊔ E) ⊓ A = Y := by
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_left hYA)
  have hx' : x ∈ ((Y ⊔ E : Subgroup X) : Set X) := hx.1
  have hxA : x ∈ A := hx.2
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Y E hEY] at hx'
  obtain ⟨y, hy, e, he, rfl⟩ := Set.mem_mul.mp hx'
  have heA : e ∈ A := by
    have := A.mul_mem (A.inv_mem (hYA hy)) hxA
    simpa using this
  have he1 : e = 1 := by
    have h : e ∈ E ⊓ A := ⟨he, heA⟩
    rw [hEA] at h
    exact Subgroup.mem_bot.mp h
  rw [he1, mul_one]
  exact hy

theorem exists_two_element_not_mem_centerOf [Finite X] {K : Subgroup X}
    (hK : CFSG.Open.IsQuasisimple K) : ∃ k ∈ K, (∃ n : ℕ, k ^ (2 ^ n) = 1) ∧
      k ∉ AschbacherTheorem3.centerOf K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 K) := inferInstance
  have h := AschbacherToolkit.sylow_not_le_center hK P
  rw [IsConcreteLE.not_le_iff_exists] at h
  obtain ⟨p, hpP, hpZ⟩ := h
  obtain ⟨n, hn⟩ := P.isPGroup' ⟨p, hpP⟩
  have h1 : p ^ 2 ^ n = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  have h2 : (p : X) ^ 2 ^ n = 1 := by
    have := congrArg Subtype.val h1
    simpa using this
  refine ⟨p, p.2, ⟨n, h2⟩, fun hp => hpZ ?_⟩
  have hpC : (p : X) ∈ Subgroup.centralizer (K : Set X) := hp.2
  rw [Subgroup.mem_center_iff]
  intro q
  exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hpC) q q.2)

variable [Finite X]

theorem isSylowOf_sup_of_odd {P E : Subgroup X} (hEP : E ≤ Subgroup.normalizer (P : Set X))
    (hP : Odd (Nat.card P)) (hE : IsPGroup 2 E) (hPE : P ⊓ E = ⊥) : IsSylowOf 2 E (P ⊔ E) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowOf_iff]
  refine ⟨le_sup_right, hE, ?_⟩
  have hcard := AschbacherTheorem3.card_sup_of_le_normalizer hEP hPE
  have hrel := Subgroup.relIndex_mul_card E (P ⊔ E)
  rw [inf_eq_left.mpr le_sup_right, hcard] at hrel
  have hrelP : E.relIndex (P ⊔ E) = Nat.card P := Nat.eq_of_mul_eq_mul_right Nat.card_pos hrel
  rw [hrelP]
  exact fun h2 => (Nat.not_even_iff_odd.mpr hP) (even_iff_two_dvd.mpr h2)

theorem isSolvable_sup_of_odd {P E : Subgroup X} (hEP : E ≤ Subgroup.normalizer (P : Set X))
    (hP : Odd (Nat.card P)) (hE : IsPGroup 2 E) (hPE : P ⊓ E = ⊥) :
    Group.IsSolvable (P ⊔ E : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPle : P ≤ P ⊔ E := le_sup_left
  have hn : (P.subgroupOf (P ⊔ E)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPle).mpr (sup_le Subgroup.le_normalizer hEP)
  have hNcard : Nat.card (P.subgroupOf (P ⊔ E)) = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPle).toEquiv
  have : Group.IsSolvable (P.subgroupOf (P ⊔ E)) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (by rw [hNcard]; exact hP)
  have hcard := AschbacherTheorem3.card_sup_of_le_normalizer hEP hPE
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hE
  have hQcard : Nat.card ((P ⊔ E : Subgroup X) ⧸ P.subgroupOf (P ⊔ E)) = 2 ^ k := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (P.subgroupOf (P ⊔ E))
    rw [hcard, hNcard, hk] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h.symm.trans (mul_comm _ _))
  have : Group.IsNilpotent ((P ⊔ E : Subgroup X) ⧸ P.subgroupOf (P ⊔ E)) :=
    (IsPGroup.of_card hQcard).isNilpotent
  exact Group.isSolvable_of_subgroup_quotient (P.subgroupOf (P ⊔ E))

theorem exists_fourGroup_mem {E : Subgroup X} (hE : IsElemAbelian 2 E) {k : ℕ} (hk : 2 ≤ k)
    (hcard : Nat.card E = 2 ^ k) {e : X} (he : e ∈ E) :
    ∃ W : Subgroup X, W ≤ E ∧ IsElemAbelian 2 W ∧ Nat.card W = 4 ∧ e ∈ W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases he1 : e = 1
  · subst he1
    obtain ⟨W, hW⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) 2
      (by rw [hcard]; exact pow_dvd_pow 2 hk : 2 ^ 2 ∣ Nat.card E)
    refine ⟨W.map E.subtype, Subgroup.map_subtype_le _,
      SixConj.isElemAbelian_of_le (Subgroup.map_subtype_le _) hE, ?_, Subgroup.one_mem _⟩
    rw [Subgroup.card_map_of_injective E.subtype_injective, hW]
    norm_num
  have he2 : e ^ 2 = 1 := hE.2 e he
  have hlt : Subgroup.zpowers e < E := by
    refine lt_of_le_of_ne (Subgroup.zpowers_le.mpr he) fun h => ?_
    have h1 : Nat.card (Subgroup.zpowers e) = Nat.card E := by rw [h]
    rw [Nat.card_zpowers, orderOf_eq_prime he2 he1, hcard] at h1
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  obtain ⟨f, hfE, hfz⟩ := IsConcreteLE.exists_of_lt hlt
  have hf1 : f ≠ 1 := fun h => hfz (by rw [h]; exact Subgroup.one_mem _)
  have hfe : e ≠ f := fun h => hfz (by rw [← h]; exact Subgroup.mem_zpowers e)
  have hcomm : e * f = f * e := congrArg Subtype.val (hE.1.is_comm.comm ⟨e, he⟩ ⟨f, hfE⟩)
  have hWE : Subgroup.zpowers e ⊔ Subgroup.zpowers f ≤ E :=
    sup_le (Subgroup.zpowers_le.mpr he) (Subgroup.zpowers_le.mpr hfE)
  exact ⟨_, hWE, SixConj.isElemAbelian_of_le hWE hE,
    SixTools.card_sup_zpowers he2 (hE.2 f hfE) he1 hf1 hfe hcomm,
    Subgroup.mem_sup_left (Subgroup.mem_zpowers e)⟩

end Abstract

section Components

variable {X : Type} [Group X] {m : ℕ} {K : Fin m → Subgroup X} {B : Subgroup X}

theorem le_normalizer_of_iSup (hcomm : ∀ l l', l ≠ l' → ∀ x ∈ K l, ∀ y ∈ K l', x * y = y * x)
    (hgen : ⨆ l, K l = B) (l : Fin m) : B ≤ Subgroup.normalizer (K l : Set X) := by
  rw [← hgen]
  refine iSup_le fun l' => ?_
  by_cases h : l' = l
  · subst h
    exact Subgroup.le_normalizer
  · refine le_trans (fun x hx => ?_) (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.mem_centralizer_iff]
    exact fun y hy => hcomm l l' (Ne.symm h) y hy x hx

theorem centerOf_le_centralizer
    (hcomm : ∀ l l', l ≠ l' → ∀ x ∈ K l, ∀ y ∈ K l', x * y = y * x)
    (hgen : ⨆ l, K l = B) (l : Fin m) :
    AschbacherTheorem3.centerOf (K l) ≤ Subgroup.centralizer (B : Set X) := by
  intro z hz
  have hzK : z ∈ K l := hz.1
  have hzC : z ∈ Subgroup.centralizer (K l : Set X) := hz.2
  have hle : ⨆ l', K l' ≤ Subgroup.centralizer ({z} : Set X) := by
    refine iSup_le fun l' y hy => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    by_cases h : l' = l
    · subst h
      exact (Subgroup.mem_centralizer_iff.mp hzC) y hy
    · exact hcomm l' l h y hy z hzK
  rw [hgen] at hle
  rw [Subgroup.mem_centralizer_iff]
  exact fun y hy => Subgroup.mem_centralizer_singleton_iff.mp (hle hy)

theorem isComponentOf_of_iSup (hK : ∀ l, IsComponentOf (K l) ⊤)
    (hcomm : ∀ l l', l ≠ l' → ∀ x ∈ K l, ∀ y ∈ K l', x * y = y * x)
    (hgen : ⨆ l, K l = B) (l : Fin m) : IsComponentOf (K l) B := by
  have hle : K l ≤ B := by
    rw [← hgen]
    exact le_iSup K l
  exact ⟨hle, IsSubnormal.step hle ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr
    (le_normalizer_of_iSup hcomm hgen l)) (IsSubnormal.refl B), (hK l).2.2⟩

theorem layer_eq_top_of_iSup (hK : ∀ l, IsComponentOf (K l) ⊤)
    (hcomm : ∀ l l', l ≠ l' → ∀ x ∈ K l, ∀ y ∈ K l', x * y = y * x)
    (hgen : ⨆ l, K l = B) : Layer.subgroup B = ⊤ := by
  have hleB : ∀ l, K l ≤ B := fun l => by
    rw [← hgen]
    exact le_iSup K l
  have hcomp : ∀ l, IsComponentOf ((K l).subgroupOf B) ⊤ := by
    intro l
    have hn : ((K l).subgroupOf B).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (hleB l)).mpr
        (le_normalizer_of_iSup hcomm hgen l)
    refine ⟨le_top, IsSubnormal.step le_top ?_ (IsSubnormal.refl ⊤),
      Components.quasisimple_of_equiv (Subgroup.subgroupOfEquivOfLe (hleB l)) (hK l).2.2⟩
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_top]
    exact (Subgroup.normalizer_eq_top_iff.mpr hn).ge
  apply top_unique
  intro x _
  have hmap : ∀ l, K l ≤ (Layer.subgroup B).map B.subtype := fun l y hy =>
    ⟨⟨y, hleB l hy⟩, Layer.component_le (hcomp l) hy, rfl⟩
  have hxB : (x : X) ∈ ⨆ l, K l := by
    rw [hgen]
    exact x.2
  obtain ⟨y, hy, hyx⟩ := iSup_le hmap hxB
  rwa [show y = x from Subtype.ext hyx] at hy

end Components

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem exists_two_lift {W : Subgroup G} (hWH : W ≤ Subgroup.normalizer (D : Set G))
    {x : Bar D} (hx : x ∈ bar D W) (hx2 : ∃ n : ℕ, x ^ (2 ^ n) = 1) :
    ∃ w : Subgroup.normalizer (D : Set G), (w : G) ∈ W ∧ (∃ n : ℕ, (w : G) ^ (2 ^ n) = 1) ∧
      toBar D w = x := by
  obtain ⟨n, hn⟩ := hx2
  obtain ⟨V, hVW, hV2, hVx⟩ := lift_two_subgroup hWH (isPGroup_zpowers_of_pow hn)
    (Subgroup.zpowers_le.mpr hx)
  have hxV : x ∈ bar D V := by
    rw [hVx]
    exact Subgroup.mem_zpowers x
  obtain ⟨w, hwV, rfl⟩ := (mem_bar_iff D V _).mp hxV
  obtain ⟨k, hk⟩ := hV2 ⟨w, hwV⟩
  refine ⟨w, hVW hwV, ⟨k, ?_⟩, rfl⟩
  have := congrArg Subtype.val hk
  simpa using this

omit [Finite G] in
theorem mem_factorZStar_iff {i : Fin r} {w : Subgroup.normalizer (D : Set G)}
    (hw : (w : G) ∈ aschbacherThm5Preimage D (Abar i)) :
    (w : G) ∈ factorZStar D Abar i ↔ toBar D w ∈
      Subgroup.centralizer (bar D (aschbacherThm5Preimage D (Abar i)) : Set (Bar D)) := by
  rw [← centralizes_iff_mem_centralizer D _ (preimage_le D _)]
  constructor
  · intro h
    exact centralizes_of_mem_centralizing h.2
  · intro h
    exact ⟨hw, (mem_centralizing_iff _ _).mpr ⟨preimage_le D _ hw, h⟩⟩

theorem exists_outer_of_moved {i : Fin r} {g e : G}
    (heH : e ∈ Subgroup.normalizer (D : Set G))
    (heA : e ∈ Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G))
    (he2 : orderOf e = 2)
    (hCe : Subgroup.centralizer ({e} : Set G) ≤
      rightConjugate (Subgroup.normalizer (D : Set G)) g)
    {K : Subgroup (Bar D)} (hK : IsComponentOf K ⊤)
    (hKA : K ≤ bar D (aschbacherThm5Preimage D (Abar i)))
    (hKe : toBar D ⟨e, heH⟩ ∉ Subgroup.normalizer (K : Set (Bar D))) :
    ∃ x ∈ aschbacherThm5Preimage D (Abar i) ⊓ rightConjugate (Subgroup.normalizer (D : Set G)) g,
      x ∉ factorZStar D Abar i ∧ ∃ k : ℕ, x ^ (2 ^ k) = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAH : aschbacherThm5Preimage D (Abar i) ≤ Subgroup.normalizer (D : Set G) :=
    (preimage_le D _).trans Subgroup.le_normalizer
  set ē := toBar D ⟨e, heH⟩ with hēdef
  have hē2 : ē ^ 2 = 1 := by
    have h1 : (⟨e, heH⟩ : Subgroup.normalizer (D : Set G)) ^ 2 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, ← he2, pow_orderOf_eq_one]; rfl)
    rw [hēdef, ← map_pow, h1, map_one]
  have hee : ē * ē = 1 := by rw [← pow_two]; exact hē2
  have hēinv : ē⁻¹ = ē := inv_eq_of_mul_eq_one_right hee
  have hK' : IsComponentOf (K.map (MulAut.conj ē).toMonoidHom) ⊤ :=
    (LocalComponents.equiv_iff (MulAut.conj ē) K).mpr hK
  have hne : K.map (MulAut.conj ē).toMonoidHom ≠ K :=
    fun h => hKe (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
  have hK'C : K.map (MulAut.conj ē).toMonoidHom ≤ Subgroup.centralizer (K : Set (Bar D)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (LocalComponents.commute_of_ne _ K hK' hK hne)
  obtain ⟨k, hkK, ⟨n, hn⟩, hkZ⟩ := exists_two_element_not_mem_centerOf hK.2.2
  have hk'K' : ē * k * ē⁻¹ ∈ K.map (MulAut.conj ē).toMonoidHom := ⟨k, hkK, by simp⟩
  have hkk' : k * (ē * k * ē⁻¹) = ē * k * ē⁻¹ * k :=
    (Subgroup.mem_centralizer_iff.mp (hK'C hk'K')) k hkK
  have hdA : k * (ē * k * ē⁻¹) ∈ bar D (aschbacherThm5Preimage D (Abar i)) := by
    have hēN : ē ∈ Subgroup.normalizer (bar D (aschbacherThm5Preimage D (Abar i)) : Set (Bar D)) :=
      toBar_mem_normalizer_bar hAH heA
    exact Subgroup.mul_mem _ (hKA hkK) ((Subgroup.mem_normalizer_iff.mp hēN k).mp (hKA hkK))
  have hdC : k * (ē * k * ē⁻¹) ∈ Subgroup.centralizer ({ē} : Set (Bar D)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc k * (ē * k * ē⁻¹) * ē = k * ē * k := by group
      _ = k * ē⁻¹ * k := by rw [hēinv]
      _ = ē * ē * k * ē⁻¹ * k := by rw [hee, one_mul]
      _ = ē * (ē * k * ē⁻¹ * k) := by group
      _ = ē * (k * (ē * k * ē⁻¹)) := by rw [hkk']
  have hd2 : (k * (ē * k * ē⁻¹)) ^ (2 ^ n) = 1 := by
    rw [(show Commute k (ē * k * ē⁻¹) from hkk').mul_pow, conj_pow, hn]
    group
  have hdZ : k * (ē * k * ē⁻¹) ∉
      Subgroup.centralizer (bar D (aschbacherThm5Preimage D (Abar i)) : Set (Bar D)) := by
    intro hdc
    apply hkZ
    refine ⟨hkK, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    have h1 := (Subgroup.mem_centralizer_iff.mp hdc) y (hKA hy)
    have h2 := (Subgroup.mem_centralizer_iff.mp (hK'C hk'K')) y hy
    have h3 : y * k * (ē * k * ē⁻¹) = k * y * (ē * k * ē⁻¹) := by
      calc y * k * (ē * k * ē⁻¹) = y * (k * (ē * k * ē⁻¹)) := by group
        _ = k * (ē * k * ē⁻¹) * y := h1
        _ = k * (ē * k * ē⁻¹ * y) := by group
        _ = k * (y * (ē * k * ē⁻¹)) := by rw [← h2]
        _ = k * y * (ē * k * ē⁻¹) := by group
    exact mul_right_cancel h3
  have hdmem : k * (ē * k * ē⁻¹) ∈
      bar D (aschbacherThm5Preimage D (Abar i) ⊓ Subgroup.centralizer ({e} : Set G)) := by
    rw [bar_inf_centralizer (core_le_preimage D _) heH he2]
    exact ⟨hdA, hdC⟩
  obtain ⟨w, hw, hw2, hwd⟩ := exists_two_lift (inf_le_left.trans hAH) hdmem ⟨n, hd2⟩
  refine ⟨w, ⟨hw.1, hCe hw.2⟩, fun hwZ => hdZ ?_, hw2⟩
  rw [← hwd]
  exact (mem_factorZStar_iff hw.1).mp hwZ

end DeltaLocal.Five

end CFSG.ComponentClassification.AschbacherTheorem5
