module

public import CFSG.LocalAnalysis.ComponentInitial.F4FieldTwoCoverCount
public import CFSG.LieType.Chevalley.ChevalleySplitBN
public import CFSG.LieType.Chevalley.SylowOpposition
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley F4FieldTwoCover
open Subgroup
open scoped commutatorElement

namespace F4FieldTwoCover

theorem height_two_nsmul_add (α β : Fin Tag.F4.rank → ℤ) :
    height (α + 2 • β) = height α + 2 * height β := by
  rw [height_add]
  congr 1
  simp only [height, Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat, Finset.mul_sum]

theorem f4Len_add (α β : Fin Tag.F4.rank → ℤ) :
    f4Len (α + β) = f4Len α + 2 * f4Ip α β + f4Len β := by
  simp only [f4Len, f4Ip, f4Euclid_add, add_dotProduct, dotProduct_add,
    dotProduct_comm (f4Euclid β)]
  ring

theorem f4Ip_add_left (α β γ : Fin Tag.F4.rank → ℤ) :
    f4Ip (α + β) γ = f4Ip α γ + f4Ip β γ := by
  simp only [f4Ip, f4Euclid_add, add_dotProduct]

theorem f4Ip_add_right (α β γ : Fin Tag.F4.rank → ℤ) :
    f4Ip α (β + γ) = f4Ip α β + f4Ip α γ := by
  simp only [f4Ip, f4Euclid_add, dotProduct_add]

theorem f4Ip_two_nsmul_right (α β : Fin Tag.F4.rank → ℤ) : f4Ip α (2 • β) = 2 * f4Ip α β := by
  rw [two_nsmul, f4Ip_add_right]
  ring

theorem f4Ip_two_nsmul_left (α β : Fin Tag.F4.rank → ℤ) : f4Ip (2 • α) β = 2 * f4Ip α β := by
  rw [two_nsmul, f4Ip_add_left]
  ring

theorem f4Len_pos {r : Fin Tag.F4.rank → ℤ} (hr : IsRoot .F4 r) : 0 < f4Len r := by
  rcases f4Len_of_isRoot hr with h | h <;> rw [h] <;> norm_num

theorem rootPair_of_len_ne {r s : Fin Tag.F4.rank → ℤ} (hr : IsRoot .F4 r) (hs : IsRoot .F4 s)
    (h : f4Len r ≠ f4Len s) : RootPair r s := by
  refine ⟨hr, hs, fun e => h (by rw [e]), fun e => h ?_⟩
  rw [e]
  simp only [f4Len, f4Euclid_neg, neg_dotProduct, dotProduct_neg, neg_neg]

end F4FieldTwoCover

theorem F4_field_two_central_two_kernel_elementary {K : Type} [Field K] (hK : Nat.card K = 2)
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E] (η : E →* adjointGroup .F4 K)
    (hη : Function.Surjective η) (hC : η.ker ≤ center E) (h2 : IsPGroup 2 η.ker) :
    (∀ c ∈ η.ker, c ^ 2 = 1) ∧ CFSG.IsElementaryAbelian 2 η.ker := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : CharP K 2 :=
    finite_field_prime_power_characteristic Nat.prime_two le_rfl (by rw [hK, pow_one])
  choose! y hy hy2 using fun r (hr : IsRoot .F4 r) => exists_lift_mul_self_xr hK hη hC hr
  have hLC := fun {r s : Fin Tag.F4.rank → ℤ} (h : RootPair r s) hrs =>
    liftsCommute_xr (η := η) hK hη hC h hrs
  set D := kerSq η hC with hD
  have : D.Normal := Subgroup.normal_of_le_center (kerSq_le_center hC)
  have hDle : D ≤ η.ker := fun c hc => hc.1
  set η' : E ⧸ D →* adjointGroup .F4 K := QuotientGroup.lift D η hDle with hη'
  have hη'mk : ∀ e : E, η' (e : E ⧸ D) = η e := fun e => QuotientGroup.lift_mk _ _ _
  set yb : (Fin Tag.F4.rank → ℤ) → E ⧸ D := fun r => (y r : E ⧸ D) with hyb
  have hmk : ∀ {a b : E}, a * b⁻¹ ∈ D → (a : E ⧸ D) = b := fun h =>
    QuotientGroup.eq_iff_div_mem.mpr (by rwa [div_eq_mul_inv])
  have hmkc : ∀ a b : E, ⁅(a : E ⧸ D), (b : E ⧸ D)⁆ = ((⁅a, b⁆ : E) : E ⧸ D) := fun a b =>
    (map_commutatorElement (QuotientGroup.mk' D) a b).symm
  set L : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ) → List (Fin Tag.F4.rank → ℤ) :=
    fun α β =>
      if f4Len α = f4Len β ∧ 2 * f4Ip α β = -f4Len α then [α + β]
      else if f4Len α = 2 ∧ f4Len β = 1 ∧ f4Ip α β = -1 then [α + β, α + 2 • β]
      else if f4Len α = 1 ∧ f4Len β = 2 ∧ f4Ip α β = -1 then [β + α, β + 2 • α]
      else [] with hLdef
  have hmixed : ∀ {α β : Fin Tag.F4.rank → ℤ}, RootPair α β → f4Len α = 2 → f4Len β = 1 →
      f4Ip α β = -1 → IsRoot .F4 (α + β) ∧ IsRoot .F4 (α + 2 • β) ∧
        ⁅yb α, yb β⁆ = yb (α + β) * yb (α + 2 • β) ∧
        yb (α + β) * yb (α + 2 • β) * (yb (α + β) * yb (α + 2 • β)) = 1 := by
    intro α β h hA hB hip
    obtain ⟨h1, h2, h3, h4, h5, -⟩ := xr_commutatorElement_mixed (K := K) hK h hA hB hip
    have hAA : f4Ip α α = 2 := hA
    have hBB : f4Ip β β = 1 := hB
    have hl1 : f4Ip α (α + β) = 1 := by
      rw [f4Ip_add_right, hip, hAA]
      norm_num
    have hl2 : f4Ip α (α + 2 • β) = 0 := by
      rw [f4Ip_add_right, f4Ip_two_nsmul_right, hip, hAA]
      norm_num
    have hl3 : f4Ip (α + β) (α + 2 • β) = 1 := by
      rw [f4Ip_add_left, f4Ip_add_right, f4Ip_add_right, f4Ip_two_nsmul_right,
        f4Ip_two_nsmul_right, hip, f4Ip_comm β α, hip, hAA, hBB]
      norm_num
    have hc1 := hLC (rootPair_of_ip h.1 h1 (by rw [hl1, hA]; norm_num)
      (by rw [hl1, hA]; norm_num)) (Or.inr (Or.inr (Or.inr ⟨hA, h3, Or.inr hl1⟩)))
    have hc2 := hLC (rootPair_of_ip h.1 h2 (by rw [hl2, hA]; norm_num)
      (by rw [hl2, hA]; norm_num)) (Or.inr (Or.inl ⟨hA, h4, hl2⟩))
    have hc3 := hLC (rootPair_of_len_ne h1 h2 (by rw [h3, h4]; norm_num))
      (Or.inr (Or.inr (Or.inl ⟨h3, h4, Or.inr hl3⟩)))
    have hrel := commutatorElement_mul_inv_mem_kerSq_of_mul hC (hy α h.1) (hy β h.2.1)
      (hy _ h1) (hy _ h2) (hy2 α h.1) (hy2 _ h1) (hy2 _ h2) h5 hc1 hc2 hc3
    refine ⟨h1, h2, ?_, ?_⟩
    · rw [hyb, hmkc, ← QuotientGroup.mk_mul]
      exact hmk hrel
    · have := mul_self_of_mul_self_of_commute (hy2 _ h1) (hy2 _ h2) (hc3 _ _ (hy _ h1) (hy _ h2))
      simp only [hyb, ← QuotientGroup.mk_mul, this, QuotientGroup.mk_one]
  have hpair : ∀ {α β : Fin Tag.F4.rank → ℤ}, IsRoot .F4 α → 0 < height α → IsRoot .F4 β →
      0 < height β → α ≠ β → RootPair α β := by
    intro α β hα hαp hβ hβp hne
    refine ⟨hα, hβ, hne, fun h => ?_⟩
    have : height α = -height β := by
      rw [h]
      simp [height]
    omega
  have hrel : ∀ α β, IsRoot .F4 α → 0 < height α → IsRoot .F4 β → 0 < height β → α ≠ β →
      ⁅yb α, yb β⁆ = ((L α β).map yb).prod := by
    intro α β hα hαp hβ hβp hne
    have h := hpair hα hαp hβ hβp hne
    by_cases c1 : f4Len α = f4Len β ∧ 2 * f4Ip α β = -f4Len α
    · simp only [hLdef, ite_eq_left c1, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one]
      obtain ⟨h1, h2⟩ := xr_commutatorElement_obtuse (K := K) hK h c1.1 c1.2
      have hlen : f4Len (α + β) = f4Len α := by
        rw [f4Len_add]
        linarith [c1.1, c1.2]
      have hip : 2 * f4Ip (α + β) α = f4Len (α + β) := by
        rw [f4Ip_add_left, hlen, f4Ip_comm β α]
        have : f4Ip α α = f4Len α := rfl
        linarith [c1.2]
      have hpos := f4Len_pos hα
      have hc := hLC (rootPair_of_ip h1 hα (by linarith) (by linarith)) (Or.inl ⟨hlen, hip⟩)
      rw [hyb, hmkc]
      exact hmk (commutatorElement_mul_inv_mem_kerSq hC (hy α hα) (hy β hβ) (hy _ h1)
        (hy2 α hα) (hy2 _ h1) h2 hc)
    · by_cases c2 : f4Len α = 2 ∧ f4Len β = 1 ∧ f4Ip α β = -1
      · simp only [hLdef, ite_eq_right c1, ite_eq_left c2, List.map_cons, List.map_nil,
          List.prod_cons, List.prod_nil, mul_one]
        exact (hmixed h c2.1 c2.2.1 c2.2.2).2.2.1
      · by_cases c3 : f4Len α = 1 ∧ f4Len β = 2 ∧ f4Ip α β = -1
        · simp only [hLdef, ite_eq_right c1, ite_eq_right c2, ite_eq_left c3, List.map_cons,
            List.map_nil, List.prod_cons, List.prod_nil, mul_one]
          obtain ⟨-, -, hm, hsq⟩ := hmixed h.symm c3.2.1 c3.1 (by rw [f4Ip_comm]; exact c3.2.2)
          rw [← commutatorElement_inv, hm]
          exact inv_eq_of_mul_eq_one_right hsq
        · simp only [hLdef, ite_eq_right c1, ite_eq_right c2, ite_eq_right c3, List.map_nil,
            List.prod_nil]
          have hcomm := xr_commute (K := K) hK h c1 c2 c3
          have hk := commutatorElement_mem_kerSq_of_commute hC (a := y α) (b := y β)
            (by rw [hy α hα, hy β hβ]; exact hcomm) (by rw [hy α hα]; exact xr_mul_self hK hα)
          rw [hyb, hmkc]
          exact (QuotientGroup.eq_one_iff _).mpr hk
  have hL : ∀ α β, IsRoot .F4 α → 0 < height α → IsRoot .F4 β → 0 < height β → α ≠ β →
      ∀ γ ∈ L α β, IsRoot .F4 γ ∧ height α < height γ ∧ height β < height γ := by
    intro α β hα hαp hβ hβp hne γ hγ
    have h := hpair hα hαp hβ hβp hne
    by_cases c1 : f4Len α = f4Len β ∧ 2 * f4Ip α β = -f4Len α
    · simp only [hLdef, ite_eq_left c1, List.mem_singleton] at hγ
      subst hγ
      refine ⟨(xr_commutatorElement_obtuse (K := K) hK h c1.1 c1.2).1, ?_, ?_⟩ <;>
        rw [height_add] <;> omega
    · by_cases c2 : f4Len α = 2 ∧ f4Len β = 1 ∧ f4Ip α β = -1
      · simp only [hLdef, ite_eq_right c1, ite_eq_left c2, List.mem_cons, List.not_mem_nil,
          or_false] at hγ
        obtain ⟨h1, h2, -⟩ := hmixed h c2.1 c2.2.1 c2.2.2
        rcases hγ with rfl | rfl
        · exact ⟨h1, by rw [height_add]; omega, by rw [height_add]; omega⟩
        · exact ⟨h2, by rw [height_two_nsmul_add]; omega, by rw [height_two_nsmul_add]; omega⟩
      · by_cases c3 : f4Len α = 1 ∧ f4Len β = 2 ∧ f4Ip α β = -1
        · simp only [hLdef, ite_eq_right c1, ite_eq_right c2, ite_eq_left c3, List.mem_cons,
            List.not_mem_nil, or_false] at hγ
          obtain ⟨h1, h2, -⟩ := hmixed h.symm c3.2.1 c3.1 (by rw [f4Ip_comm]; exact c3.2.2)
          rcases hγ with rfl | rfl
          · exact ⟨h1, by rw [height_add]; omega, by rw [height_add]; omega⟩
          · exact ⟨h2, by rw [height_two_nsmul_add]; omega, by rw [height_two_nsmul_add]; omega⟩
        · simp only [hLdef, ite_eq_right c1, ite_eq_right c2, ite_eq_right c3,
            List.not_mem_nil] at hγ
  have hcount := card_closure_le_of_posRoots_list yb (fun α hα _ => by
    rw [hyb, ← QuotientGroup.mk_mul, hy2 α hα, QuotientGroup.mk_one]) L hL hrel
  set P₀ := closure {g | ∃ α, IsRoot .F4 α ∧ 0 < height α ∧ yb α = g} with hP₀
  have hmap : P₀.map η' = closure {g | ∃ α, IsRoot .F4 α ∧ 0 < height α ∧ xr (K := K) α = g} := by
    rw [MonoidHom.map_closure]
    congr 1
    ext g
    constructor
    · rintro ⟨_, ⟨α, hα, hαp, rfl⟩, rfl⟩
      exact ⟨α, hα, hαp, by rw [hyb, hη'mk, hy α hα]⟩
    · rintro ⟨α, hα, hαp, rfl⟩
      exact ⟨yb α, ⟨α, hα, hαp, rfl⟩, by rw [hyb, hη'mk, hy α hα]⟩
  have := finite_modGL (τ := .F4) (K := K)
  obtain ⟨hUp, hUi⟩ := isPGroup_and_not_dvd_index 2 (posUnipotent_le_adjointGroup (K := K))
    (card_posUnipotent (τ := .F4) (K := K))
  set S := hUp.toSylow hUi with hS
  have hSle : (S : Subgroup (adjointGroup .F4 K)) ≤ P₀.map η' := by
    rw [hmap]
    exact posUnipotent_le_closure_xr hK
  have hcardS : Nat.card (S : Subgroup (adjointGroup .F4 K)) =
      2 ^ {α : Fin Tag.F4.rank → ℤ | IsRoot .F4 α ∧ 0 < height α}.ncard := by
    rw [hS, IsPGroup.toSylow_coe, card_subgroupOf_of_le (posUnipotent_le_adjointGroup (K := K)),
      card_posUnipotent, hK]
  have : Finite (P₀.map η') := Finite.of_surjective _ (η'.subgroupMap_surjective P₀)
  have hbij : Function.Bijective (η'.subgroupMap P₀) := by
    refine (η'.subgroupMap_surjective P₀).bijective_of_nat_card_le ?_
    calc Nat.card P₀ ≤ 2 ^ {α : Fin Tag.F4.rank → ℤ | IsRoot .F4 α ∧ 0 < height α}.ncard := hcount
      _ = Nat.card (S : Subgroup (adjointGroup .F4 K)) := hcardS.symm
      _ ≤ Nat.card (P₀.map η') := Subgroup.card_le_of_le hSle
  have hinj : ∀ z ∈ P₀, η' z = 1 → z = 1 := by
    intro z hz hz1
    have h : η'.subgroupMap P₀ ⟨z, hz⟩ = η'.subgroupMap P₀ 1 :=
      Subtype.ext (by rw [map_one]; exact hz1)
    exact congrArg Subtype.val (hbij.1 h)
  have hη'surj : Function.Surjective η' := by
    intro x
    obtain ⟨e, rfl⟩ := hη x
    exact ⟨e, hη'mk e⟩
  have hC' : η'.ker ≤ center (E ⧸ D) := by
    intro c hc
    induction c using QuotientGroup.induction_on with
    | H z =>
      rw [MonoidHom.mem_ker, hη'mk] at hc
      refine Subgroup.mem_center_iff.mpr fun g => ?_
      induction g using QuotientGroup.induction_on with
      | H g =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp (hC hc) g]
  have h2' : IsPGroup 2 η'.ker := by
    rintro ⟨c, hc⟩
    induction c using QuotientGroup.induction_on with
    | H z =>
      rw [MonoidHom.mem_ker, hη'mk] at hc
      obtain ⟨n, hn⟩ := h2 ⟨z, hc⟩
      refine ⟨n, Subtype.ext ?_⟩
      have hz : z ^ 2 ^ n = 1 := by simpa using congrArg (fun w : η.ker => (w : E)) hn
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [← QuotientGroup.mk_pow, hz, QuotientGroup.mk_one]
  have hbot := LinearCover.ker_eq_bot_of_sylow_le_map η' hη'surj hC' h2' S P₀ hSle hinj
  have hsq : ∀ c ∈ η.ker, c * c = 1 := by
    intro c hc
    have hc' : (c : E ⧸ D) ∈ η'.ker := by
      rw [MonoidHom.mem_ker, hη'mk]
      exact hc
    rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hc'
    exact hc'.2
  refine ⟨fun c hc => by rw [sq]; exact hsq c hc, ?_⟩
  exact { is_comm := ⟨fun u v => Subtype.ext (Subgroup.mem_center_iff.mp (hC v.2) u)⟩
          exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
            Subtype.ext (by rw [SubgroupClass.coe_pow, sq, OneMemClass.coe_one]; exact hsq x x.2) }

end CFSG.LocalAnalysis.ComponentInitial
