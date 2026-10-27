module

public import CFSG.Quasithin.Background.CommVBasics
public import CFSG.CGT.PushingUpLit.BHS.ThreeConj
public import CFSG.CGT.PushingUpLit.BHS.TwoSixteenAlt
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.Quasithin.Background.B1MoreElevenB
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.D2Conj
public import CFSG.Quasithin.Background.D2Cyclic
public import CFSG.Quasithin.EmptyFaithful.Setting

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin

local macro "comm_group" : tactic =>
  `(tactic| (apply Additive.ofMul.injective
             simp only [ofMul_mul, ofMul_inv, ofMul_div, ofMul_one]
             abel))

section Conj

variable {G : Type*} [Group G]

theorem mem_map_conjHom_iff {H : Subgroup G} {a x : G} :
    x ∈ H.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * x * a ∈ H := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem map_conjHom_eq_iff_mem_normalizer {H : Subgroup G} {a : G} :
    H.map (MulAut.conj a).toMonoidHom = H ↔ a ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, MulEquiv.toMonoidHom_eq_coe]

theorem inv_mul_mem_normalizer_of_map_conjHom_eq {H : Subgroup G} {a b : G}
    (h : H.map (MulAut.conj a).toMonoidHom = H.map (MulAut.conj b).toMonoidHom) :
    a⁻¹ * b ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 : a⁻¹ * (b * x * b⁻¹) * a ∈ H ↔ x ∈ H := by
    rw [← mem_map_conjHom_iff, h, mem_map_conjHom_iff]
    simp [mul_assoc]
  rw [show a⁻¹ * b * x * (a⁻¹ * b)⁻¹ = a⁻¹ * (b * x * b⁻¹) * a by group]
  exact h1.symm

theorem card_map_conjHom (H : Subgroup G) (a : G) :
    Nat.card (H.map (MulAut.conj a).toMonoidHom) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj a).injective

theorem map_conjHom_le {H N : Subgroup G} {a : G} (ha : ∀ n ∈ N, a * n * a⁻¹ ∈ N) (hH : H ≤ N) :
    H.map (MulAut.conj a).toMonoidHom ≤ N := by
  rintro _ ⟨h, hh, rfl⟩
  exact ha h (hH hh)

end Conj

variable {V : Type} [CommGroup V]

theorem mem_fixV_map_conj {E : Subgroup (MulAut V)} {a : MulAut V} {v : V} (hv : v ∈ fixV E)
    (ha : a v = v) : v ∈ fixV (E.map (MulAut.conj a).toMonoidHom) := by
  intro y hy
  obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hy
  have ha' : a⁻¹ v = v := by
    have h1 : a⁻¹ (a v) = v := by simp
    rwa [ha] at h1
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.mul_apply, ha', hv e he, ha]

theorem map_mem_fixV_of_mem_normalizer {E : Subgroup (MulAut V)} {x : MulAut V}
    (hx : x ∈ Subgroup.normalizer (E : Set (MulAut V))) {v : V} (hv : v ∈ fixV E) :
    x v ∈ fixV E :=
  CFSG.Quasithin.fixV_apply_mem_of_mem_normalizer hx hv

theorem odd_card_of_isPGroup_three {N P : Subgroup (MulAut V)} (hN : IsPGroup 3 N) (hP : P ≤ N)
    [Finite P] : Odd (Nat.card P) := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (hN.to_le hP)
  rw [hk]
  exact Odd.pow (by decide)

variable [Finite V]

theorem commV_inf_fixV_of_odd (hV : ∀ v : V, v ^ 2 = 1) {P : Subgroup (MulAut V)}
    (hP : Odd (Nat.card P)) : commV P ⊓ fixV P = ⊥ := by
  have h := (coprime_decomp hP hV (W := ⊤) fun _ _ _ _ => Subgroup.mem_top _).2
  rwa [← commV_eq_commSub, top_inf_eq] at h

theorem mem_normalizer_of_forall_commV (hV : ∀ v : V, v ^ 2 = 1) {E N : Subgroup (MulAut V)}
    (hN : IsPGroup 3 N) (hEN : E ≤ N) (hE : Nat.card E = 3) (hW : Nat.card (commV E) = 4)
    {x : MulAut V} (hxN : ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hxW : ∀ w ∈ commV E, x w = w) :
    x ∈ Subgroup.normalizer (E : Set (MulAut V)) := by
  rw [← map_conjHom_eq_iff_mem_normalizer]
  by_contra hne
  have hmap : commV (E.map (MulAut.conj x).toMonoidHom) = commV E := by
    rw [B19.commV_map_conj]
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      simpa [hxW u hu] using hu
    · intro hv
      exact ⟨v, hv, by simp [hxW v hv]⟩
  have h := (conj_three_commute hV hN hEN (map_conjHom_le hxN hEN) hE
    ((card_map_conjHom E x).trans hE) hW (hmap ▸ hW) (Ne.symm hne)).1
  rw [hmap, inf_idem] at h
  rw [h, Subgroup.card_bot] at hW
  exact absurd hW (by norm_num)

theorem relIndex_mul_card_fixV_le_four (hV : ∀ v : V, v ^ 2 = 1) {K : Subgroup (MulAut V)}
    {W : Subgroup V} (hK : K ≤ stabSub W) (hK2 : ∀ k ∈ K, k ^ 2 = 1) (hW : Nat.card W = 4) :
    (cenIn K W).relIndex K * Nat.card ↥(W ⊓ fixV K) ≤ 4 := by
  have h1 := card_autSub_mul hK
  have h2 := Subgroup.relIndex_mul_card (cenIn K W) K
  rw [inf_eq_left.2 (cenIn_le K W), cenIn_eq_inf] at h2
  have hrel : (cenIn K W).relIndex K = Nat.card (autSub K W) :=
    Nat.eq_of_mul_eq_mul_right Nat.card_pos (h2.trans h1.symm)
  have h6 : Nat.card (autSub K W) ∣ 2 * 3 := by
    have h := Subgroup.card_subgroup_dvd_card (autSub K W)
    rw [card_mulAut_eq (fun u => Subtype.ext (hV u)), rk_eq_two_of_card_eq_four hW] at h
    have hp : ∏ i : Fin 2, (2 ^ 2 - 2 ^ (i : ℕ)) = 2 * 3 := by decide
    rwa [hp] at h
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.1
    (isPGroup_two_of_sq_eq_one (fun k : K => Subtype.ext (hK2 k k.2)))
  have hdvdK : Nat.card (autSub K W) ∣ 2 ^ j := hj ▸ Dvd.intro _ h1
  have hcop : Nat.Coprime (Nat.card (autSub K W)) 3 :=
    Nat.Coprime.coprime_dvd_left hdvdK (Nat.Coprime.pow_left j (by norm_num))
  have hle2 : (cenIn K W).relIndex K ≤ 2 :=
    hrel ▸ Nat.le_of_dvd (by norm_num) (hcop.dvd_of_dvd_mul_right h6)
  by_cases hfix : W ≤ fixV K
  · have h1' : (cenIn K W).relIndex K = 1 :=
      Subgroup.relIndex_eq_one.2 fun k hk => ⟨hk, fun w hw => hfix hw k hk⟩
    rw [h1', one_mul, ← hW]
    exact Subgroup.card_le_of_le inf_le_left
  · have hd : Nat.card ↥(W ⊓ fixV K) ∣ 4 := hW ▸ Subgroup.card_dvd_of_le inf_le_left
    have hne : Nat.card ↥(W ⊓ fixV K) ≠ 4 := by
      intro h4
      apply hfix
      have := Subgroup.eq_of_le_of_card_ge (inf_le_left : W ⊓ fixV K ≤ W) (by rw [hW, h4])
      rw [← this]
      exact inf_le_right
    have hle4 := Nat.le_of_dvd (by norm_num) hd
    have hlt : Nat.card ↥(W ⊓ fixV K) ≤ 2 := by
      generalize Nat.card ↥(W ⊓ fixV K) = c at hd hne hle4
      interval_cases c <;> omega
    calc (cenIn K W).relIndex K * Nat.card ↥(W ⊓ fixV K) ≤ 2 * 2 := Nat.mul_le_mul hle2 hlt
      _ = 4 := by norm_num

theorem card_inf_fixV_le_of_proj (hV : ∀ v : V, v ^ 2 = 1) {A E K : Subgroup (MulAut V)}
    {U : Subgroup V} (hE : Odd (Nat.card E)) (hKA : K ≤ A)
    (hKN : K ≤ Subgroup.normalizer (E : Set (MulAut V)))
    (hU : ∀ w ∈ U, w ∈ fixV A → w ∈ fixV E → w = 1) :
    Nat.card ↥(U ⊓ fixV A) ≤ Nat.card ↥(commV E ⊓ fixV K) := by
  let π : V →* V := MonoidHom.id V * avgMap E
  have hπ : ∀ v, π v = v * avgMap E v := fun v => rfl
  have hπW : ∀ v, π v ∈ commV E := fun v => mul_avgMap_mem_commV hE hV v
  have hdec := commV_inf_fixV_of_odd hV hE
  have hπK : ∀ w ∈ fixV A, π w ∈ fixV K := by
    intro w hw x hx
    have hq : avgMap E w ∈ fixV E := avgMap_mem_fixV E w
    have hxp : x (π w) ∈ commV E := B15P4.map_commV_mem (hKN hx) _ (hπW w)
    have hxq : x (avgMap E w) ∈ fixV E := map_mem_fixV_of_mem_normalizer (hKN hx) hq
    have hxw : x (π w) * (x (avgMap E w))⁻¹ = π w * (avgMap E w)⁻¹ := by
      have h0 : π w * (avgMap E w)⁻¹ = w := by rw [hπ]; group
      rw [← map_inv, ← map_mul, h0]
      exact hw x (hKA hx)
    have heq : x (π w) * (π w)⁻¹ = x (avgMap E w) * (avgMap E w)⁻¹ := by
      calc x (π w) * (π w)⁻¹
          = x (π w) * (x (avgMap E w))⁻¹ * (x (avgMap E w) * (π w)⁻¹) := by group
        _ = π w * (avgMap E w)⁻¹ * (x (avgMap E w) * (π w)⁻¹) := by rw [hxw]
        _ = x (avgMap E w) * (avgMap E w)⁻¹ := by comm_group
    have hmem : x (π w) * (π w)⁻¹ ∈ commV E ⊓ fixV E :=
      Subgroup.mem_inf.2 ⟨mul_mem hxp (inv_mem (hπW w)), heq ▸ mul_mem hxq (inv_mem hq)⟩
    rw [hdec, Subgroup.mem_bot] at hmem
    exact mul_inv_eq_one.1 hmem
  let f : ↥(U ⊓ fixV A) → ↥(commV E ⊓ fixV K) := fun w => ⟨π w, hπW w, hπK w w.2.2⟩
  refine Nat.card_le_card_of_injective f fun w₁ w₂ h12 => ?_
  have h1 : π ((w₁ : V) * (w₂ : V)⁻¹) = 1 := by
    rw [map_mul, map_inv]
    exact mul_inv_eq_one.2 (congrArg Subtype.val h12)
  have hmem : (w₁ : V) * (w₂ : V)⁻¹ ∈ U ⊓ fixV A := mul_mem w₁.2 (inv_mem w₂.2)
  have hfixE : (w₁ : V) * (w₂ : V)⁻¹ ∈ fixV E := by
    rw [hπ] at h1
    rw [eq_inv_of_mul_eq_one_left h1]
    exact inv_mem (avgMap_mem_fixV E _)
  exact Subtype.ext (mul_inv_eq_one.1 (hU _ hmem.1 hmem.2 hfixE))

theorem offender_le_normalizer_of_card_three (hV : ∀ v : V, v ^ 2 = 1)
    {A E N : Subgroup (MulAut V)} (hA : IsOff A)
    (hN : IsPGroup 3 N) (hAN : ∀ a ∈ A, ∀ n ∈ N, a * n * a⁻¹ ∈ N) (hEN : E ≤ N)
    (hE : Nat.card E = 3) (hW : Nat.card (commV E) = 4) :
    A ≤ Subgroup.normalizer (E : Set (MulAut V)) := by
  classical
  have hAe : IsElemAbelian2 A := hA.2.2.1
  set Nm := Subgroup.normalizer (E : Set (MulAut V)) with hNm
  set K := Nm ⊓ A with hKdef
  let ι := ↥A ⧸ Nm.subgroupOf A
  have : Fintype ι := Fintype.ofFinite ι
  have : Nonempty ι := ⟨((1 : ↥A) : ι)⟩
  let r : ι → MulAut V := fun i => ((Quotient.out i : ↥A) : MulAut V)
  have hr : ∀ i, r i ∈ A := fun i => (Quotient.out i).2
  let F : ι → Subgroup (MulAut V) := fun i => E.map (MulAut.conj (r i)).toMonoidHom
  have hFN : ∀ i, F i ≤ N := fun i => map_conjHom_le (hAN _ (hr i)) hEN
  have hFc : ∀ i, Nat.card (F i) = 3 := fun i => (card_map_conjHom E (r i)).trans hE
  have hFW : ∀ i, Nat.card (commV (F i)) = 4 := fun i => by
    rw [B19.commV_map_conj, Subgroup.card_map_of_injective (r i).injective, hW]
  have hFinj : ∀ i j, F i = F j → i = j := by
    intro i j hij
    have h1 : ((Quotient.out i)⁻¹ * Quotient.out j : ↥A) ∈ Nm.subgroupOf A := by
      rw [Subgroup.mem_subgroupOf]
      exact inv_mul_mem_normalizer_of_map_conjHom_eq hij
    have h2 := QuotientGroup.eq.2 h1
    rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h2
  have hT2 : ∀ i j, i ≠ j → commV (F j) ≤ fixV (F i) := fun i j hij =>
    (conj_three_commute hV hN (hFN i) (hFN j) (hFc i) (hFc j) (hFW i) (hFW j)
      fun h => hij (hFinj i j h)).2.1
  have hodd : ∀ P : Subgroup (MulAut V), P ≤ N → commV P ⊓ fixV P = ⊥ := fun P hP =>
    commV_inf_fixV_of_odd hV (odd_card_of_isPGroup_three hN hP)
  have hind : iSupIndep fun i => commV (F i) := by
    intro i
    rw [disjoint_iff, eq_bot_iff, ← hodd (F i) (hFN i)]
    exact inf_le_inf_left _ (iSup₂_le fun j hj => hT2 i j (Ne.symm hj))
  set W' : Subgroup V := ⨆ i, commV (F i) with hW'def
  have hcardW' : Nat.card W' = 4 ^ Nat.card ι := by
    have h := rk_iSup_biSup_eq_sum (fun i => commV (F i)) hind Finset.univ
    have hW'u : (⨆ i ∈ (Finset.univ : Finset ι), commV (F i)) = W' := by simp [hW'def]
    rw [hW'u] at h
    simp only [rk_eq_two_of_card_eq_four (hFW _), Finset.sum_const, Finset.card_univ,
      smul_eq_mul] at h
    rw [card_eq_two_pow hV W', h, ← Nat.card_eq_fintype_card, pow_mul']
    norm_num
  have hi₀ : r ((1 : ↥A) : ι) ∈ Nm := by
    have h := QuotientGroup.eq.1 (QuotientGroup.out_eq' ((1 : ↥A) : ι))
    rw [mul_one, Subgroup.inv_mem_iff, Subgroup.mem_subgroupOf] at h
    exact h
  have hF₀ : F ((1 : ↥A) : ι) = E := map_conjHom_eq_iff_mem_normalizer.2 hi₀
  have hWW' : commV E ≤ W' := by
    rw [← hF₀]
    exact le_iSup (fun i => commV (F i)) _
  have hCK : cenIn A (commV E) ≤ K := fun x hx =>
    Subgroup.mem_inf.2 ⟨mem_normalizer_of_forall_commV hV hN hEN hE hW
      (hAN x (mem_cenIn.1 hx).1) (mem_cenIn.1 hx).2, (mem_cenIn.1 hx).1⟩
  have hCW' : cenIn A W' = cenIn A (commV E) := by
    apply le_antisymm
    · exact fun x hx => mem_cenIn.2 ⟨(mem_cenIn.1 hx).1, fun w hw => (mem_cenIn.1 hx).2 w (hWW' hw)⟩
    · intro x hx
      obtain ⟨hxA, hxW⟩ := mem_cenIn.1 hx
      refine mem_cenIn.2 ⟨hxA, fun w hw => ?_⟩
      have hle : W' ≤ fixV (Subgroup.zpowers x) := by
        refine iSup_le fun i => ?_
        rw [B19.commV_map_conj]
        rintro _ ⟨u, hu, rfl⟩
        rw [mem_fixV_zpowers_iff]
        have hc : x * r i = r i * x := hAe.1 x hxA (r i) (hr i)
        calc x ((r i).toMonoidHom u) = (x * r i) u := rfl
          _ = (r i * x) u := by rw [hc]
          _ = (r i) (x u) := rfl
          _ = (r i).toMonoidHom u := by rw [hxW u hu]; rfl
      exact mem_fixV_zpowers_iff.1 (hle hw)
  have hKst : K ≤ stabSub (commV E) := inf_le_left.trans (normalizer_commV_le_stabSub E)
  have hK2 : ∀ k ∈ K, k ^ 2 = 1 := fun k hk => hAe.2 k (Subgroup.mem_inf.1 hk).2
  have h3 := relIndex_mul_card_fixV_le_four hV hKst hK2 hW
  have hCKe : cenIn K (commV E) = cenIn A (commV E) := by
    ext x
    simp only [mem_cenIn]
    exact ⟨fun h => ⟨(Subgroup.mem_inf.1 h.1).2, h.2⟩, fun h => ⟨hCK (mem_cenIn.2 h), h.2⟩⟩
  rw [hCKe] at h3
  have hU : ∀ w ∈ W', w ∈ fixV A → w ∈ fixV E → w = 1 := by
    intro w hw hwA hwE
    have h1 : w ∈ commV (⨆ i, F i) := by rw [B19.commV_iSup]; exact hw
    have h2 : w ∈ fixV (⨆ i, F i) := by
      rw [mem_fixV_iff_le]
      exact iSup_le fun i => mem_fixV_iff_le.1 (mem_fixV_map_conj hwE (hwA _ (hr i)))
    have h12 : w ∈ commV (⨆ i, F i) ⊓ fixV (⨆ i, F i) := Subgroup.mem_inf.2 ⟨h1, h2⟩
    rwa [hodd _ (iSup_le hFN), Subgroup.mem_bot] at h12
  have h4 := card_inf_fixV_le_of_proj hV (A := A) (odd_card_of_isPGroup_three hN hEN)
    (inf_le_right : K ≤ A) (inf_le_left : K ≤ Nm) hU
  have h1 := offender_card_le hA W'
  rw [hCW'] at h1
  have h5 := Subgroup.relIndex_mul_card (fixV A) W'
  rw [hcardW', inf_comm] at h5
  have h6 := Subgroup.relIndex_mul_relIndex (cenIn A (commV E)) K A hCK inf_le_right
  have hm' : Nm.relIndex A = Nat.card ι := rfl
  have hm : K.relIndex A = Nat.card ι := by rw [hKdef, Subgroup.inf_relIndex_right, hm']
  rw [hm] at h6
  have hle : 4 ^ Nat.card ι ≤ 4 * Nat.card ι := by
    calc 4 ^ Nat.card ι = (fixV A).relIndex W' * Nat.card ↥(W' ⊓ fixV A) := h5.symm
      _ ≤ (cenIn A (commV E)).relIndex A * Nat.card ↥(commV E ⊓ fixV K) :=
          Nat.mul_le_mul h1 h4
      _ = Nat.card ι * ((cenIn A (commV E)).relIndex K * Nat.card ↥(commV E ⊓ fixV K)) := by
          rw [← h6]; ring
      _ ≤ Nat.card ι * 4 := Nat.mul_le_mul_left _ h3
      _ = 4 * Nat.card ι := mul_comm _ _
  have hm1 : Nat.card ι = 1 := by
    have hpos : 0 < Nat.card ι := Nat.card_pos
    by_contra hne
    obtain ⟨k, hk⟩ : ∃ k, Nat.card ι = k + 2 := ⟨Nat.card ι - 2, by omega⟩
    rw [hk, pow_add] at hle
    norm_num at hle
    have hk4 : k < 4 ^ k := Nat.lt_pow_self (by norm_num)
    omega
  exact Subgroup.relIndex_eq_one.1 (hm'.trans hm1)
