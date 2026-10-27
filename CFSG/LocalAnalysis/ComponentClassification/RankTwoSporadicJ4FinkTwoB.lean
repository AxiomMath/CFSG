module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ4FinkCheck
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicYCore
public import CFSG.Sporadic.J4.QT2LocMain
public import CFSG.Sporadic.J4.QT2LocUniqCheck
public import CFSG.Sporadic.J4.QT2LocHProof
public import CFSG.Sporadic.J4.QT2LocCntProofBase

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.J4Fink

open Subgroup CFSG.ABGLocalTools CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2

theorem card_le_card_inf_centralizer_mul {G : Type*} [Group G] [Finite G] {E N : Subgroup G}
    {t : G} (hE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (ht : ∀ e ∈ E, t * e * t⁻¹ ∈ E)
    (hN : ∀ e ∈ E, e * t * e⁻¹ * t⁻¹ ∈ N) :
    Nat.card E ≤ Nat.card ↥(E ⊓ centralizer ({t} : Set G)) * Nat.card N := by
  let f : ↥E →* G := MonoidHom.mk' (fun e => (e : G) * t * (e : G)⁻¹ * t⁻¹) (fun e e' => by
    have ha : t * (e' : G)⁻¹ * t⁻¹ ∈ E := ht _ (inv_mem e'.2)
    have hb : t * (e : G)⁻¹ * t⁻¹ ∈ E := ht _ (inv_mem e.2)
    show ((e * e' : E) : G) * t * ((e * e' : E) : G)⁻¹ * t⁻¹ =
      ((e : G) * t * (e : G)⁻¹ * t⁻¹) * ((e' : G) * t * (e' : G)⁻¹ * t⁻¹)
    calc ((e * e' : E) : G) * t * ((e * e' : E) : G)⁻¹ * t⁻¹
        = (e : G) * ((e' : G) * ((t * (e' : G)⁻¹ * t⁻¹) * (t * (e : G)⁻¹ * t⁻¹))) := by
          rw [Subgroup.coe_mul]
          group
      _ = (e : G) * ((t * (e : G)⁻¹ * t⁻¹) * ((e' : G) * (t * (e' : G)⁻¹ * t⁻¹))) := by
          rw [hE _ ha _ hb, ← mul_assoc (e' : G), hE _ e'.2 _ hb, mul_assoc]
      _ = ((e : G) * t * (e : G)⁻¹ * t⁻¹) * ((e' : G) * t * (e' : G)⁻¹ * t⁻¹) := by group)
  have hker : Nat.card f.ker ≤ Nat.card ↥(E ⊓ centralizer ({t} : Set G)) := by
    refine Nat.card_le_card_of_injective
      (fun k => ⟨((k : E) : G), mem_inf.mpr ⟨(k : E).2, ?_⟩⟩) ?_
    · have hk : ((k : E) : G) * t * ((k : E) : G)⁻¹ * t⁻¹ = 1 := (MonoidHom.mem_ker).mp k.2
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hk
      rw [mem_centralizer_singleton_iff]
      exact hk
    · intro a b hab
      have h := congrArg Subtype.val hab
      simp only at h
      exact Subtype.ext (Subtype.ext h)
  have hrange : f.range ≤ N := by
    rintro _ ⟨e, rfl⟩
    exact hN e e.2
  calc Nat.card E = Nat.card f.ker * Nat.card f.range := (Subgroup.card_ker_mul_card_range f).symm
    _ ≤ Nat.card ↥(E ⊓ centralizer ({t} : Set G)) * Nat.card N :=
        Nat.mul_le_mul hker (card_le_of_le hrange)

theorem isSylowOf_P0_Hj :
    IsSylowOf 2 P0 Hj :=
  isSylowOf_of_card P0_le_Hj
    (by rw [card_P0 j4Facts.mat j4Facts, card_Hj_factorization_two j4Facts])

theorem card_Eg_inf_centralizer_le_of_P0
    {x : J} (hx : x ∈ P0)
    (hxE : x ∉ Eg uJ 11) (hsq : x * x = 1) :
    Nat.card ↥(Eg uJ 11 ⊓ centralizer ({x} : Set J)) ≤ 128 := by
  have hF := j4Facts
  have hM := hF.mat
  obtain ⟨t, htL, hxt⟩ := table_of_mem hM x hx
  have h1 : compT t t = idT := by
    have h := hxt.mul hxt
    rw [hsq] at h
    exact h.unique hM Acts.one
  have h2 : t ≠ idT := by
    intro ht
    subst ht
    apply hxE
    refine centralizer_Hj hM hF x (P0_le_Hj hx) (fun y hy => ?_)
    obtain ⟨c, hc, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 hy
    have := hxt.2 c hc
    rw [actT_idT hc] at this
    calc x * eta uJ 11 c = (x * eta uJ 11 c * x⁻¹) * x := by group
      _ = eta uJ 11 c * x := by rw [this]
  refine card_inf_le hM (fun y hy => ?_) hxt (fixCount_le t htL h1 h2)
  rw [mem_centralizer_singleton_iff] at hy
  exact hy.symm

theorem card_Eg_inf_centralizer_le
    {x : J} (hx : x ∈ Hj) (hxE : x ∉ Eg uJ 11)
    (hsq : x * x = 1) : Nat.card ↥(Eg uJ 11 ⊓ centralizer ({x} : Set J)) ≤ 128 := by
  have hM := j4Facts.mat
  have hp : IsPGroup 2 (zpowers x) := by
    have hord : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hsq)
    rcases (Nat.dvd_prime Nat.prime_two).1 hord with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; rfl)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; rfl)
  obtain ⟨k, hk, hconj⟩ := exists_conj_le_of_isSylowOf isSylowOf_P0_Hj hp (zpowers_le.mpr hx)
  have hx' : k⁻¹ * x * k ∈ P0 := hconj x (mem_zpowers x)
  have hxE' : k⁻¹ * x * k ∉ Eg uJ 11 := by
    intro hmem
    apply hxE
    have h := Hj_normalizes_Eg hM k hk _ hmem
    have e : k * (k⁻¹ * x * k) * k⁻¹ = x := by group
    rwa [e] at h
  have hsq' : (k⁻¹ * x * k) * (k⁻¹ * x * k) = 1 := by
    calc (k⁻¹ * x * k) * (k⁻¹ * x * k) = k⁻¹ * (x * x) * k := by group
      _ = 1 := by rw [hsq, mul_one, inv_mul_cancel]
  have hmap : ∀ e ∈ Eg uJ 11 ⊓ centralizer ({x} : Set J),
      k⁻¹ * e * k ∈ Eg uJ 11 ⊓ centralizer ({k⁻¹ * x * k} : Set J) := by
    intro e he
    rw [mem_inf] at he ⊢
    obtain ⟨heE, hec⟩ := he
    rw [mem_centralizer_singleton_iff] at hec ⊢
    refine ⟨?_, ?_⟩
    · have h := Hj_normalizes_Eg hM k⁻¹ (inv_mem hk) e heE
      rwa [inv_inv] at h
    · calc k⁻¹ * e * k * (k⁻¹ * x * k) = k⁻¹ * (e * x) * k := by group
        _ = k⁻¹ * (x * e) * k := by rw [hec]
        _ = k⁻¹ * x * k * (k⁻¹ * e * k) := by group
  calc Nat.card ↥(Eg uJ 11 ⊓ centralizer ({x} : Set J))
      ≤ Nat.card ↥(Eg uJ 11 ⊓ centralizer ({k⁻¹ * x * k} : Set J)) := by
        refine Nat.card_le_card_of_injective (fun e => ⟨k⁻¹ * e * k, hmap e e.2⟩) ?_
        intro a b hab
        have h := congrArg Subtype.val hab
        simp only at h
        exact Subtype.ext (mul_left_cancel (mul_right_cancel h))
    _ ≤ 128 := card_Eg_inf_centralizer_le_of_P0 hx' hxE' hsq'

theorem c2_facts {v : ℕ} (hv : v ∈ tMasks) (hv1 : v ≠ 1) :
    ∃ w ∈ c2Words, (∀ l ∈ w, l ∈ letters) ∧ actWord w 1 = 1 ∧ v ^^^ actWord w v ∈ zMasks := by
  have h := fink_c2Check
  unfold chkFinkC2 at h
  rw [Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true, List.all_eq_true,
    List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hvf : v ∈ tMasks.filter (· != 1) := List.mem_filter.mpr ⟨hv, bne_iff_ne.mpr hv1⟩
  obtain ⟨w, hw, hz⟩ := List.any_eq_true.mp (h3 v hvf)
  exact ⟨w, hw, fun l hl => List.contains_iff_mem.mp (List.all_eq_true.mp (h1 w hw) l hl),
    beq_iff_eq.mp (h2 w hw), List.contains_iff_mem.mp hz⟩

theorem false_of_twoB
    {M P : Subgroup J} (hMy : M ≤ centralizer ({eta uJ 11 1} : Set J))
    (hMn : ∀ c ∈ centralizer ({eta uJ 11 1} : Set J), ∀ m ∈ M, c * m * c⁻¹ ∈ M)
    (hP : IsSylowOf 2 P M) (hPsq : ∀ x ∈ P, x * x = 1) (hP4 : 4 ≤ Nat.card P)
    (hP2A : ∀ a ∈ P, ∀ g : J, g * eta uJ 11 3 * g⁻¹ ≠ a) : False := by
  have hM := j4Facts.mat
  have hel := elem_uJ hM
  have hCH : ∀ c ∈ centralizer ({eta uJ 11 1} : Set J), c ∈ Hj := by
    intro c hc
    rw [mem_centralizer_singleton_iff] at hc
    exact centralizer_eta_one_le_Hj hc
  have hEy : ∀ e ∈ Eg uJ 11, e ∈ centralizer ({eta uJ 11 1} : Set J) := by
    intro e he
    rw [mem_centralizer_singleton_iff]
    exact Eg_comm hel he (eta_mem_Eg 11 le_rfl 1)
  have hMEn : ∀ c ∈ centralizer ({eta uJ 11 1} : Set J), ∀ x ∈ M ⊓ Eg uJ 11,
      c * x * c⁻¹ ∈ M ⊓ Eg uJ 11 := by
    intro c hc x hx
    rw [mem_inf] at hx ⊢
    exact ⟨hMn c hc x hx.1, Hj_normalizes_Eg hM c (hCH c hc) x hx.2⟩
  have hMEP : M ⊓ Eg uJ 11 ≤ P := by
    have hnorm : M ≤ normalizer ((M ⊓ Eg uJ 11 : Subgroup J) : Set J) := by
      intro m hm
      rw [mem_normalizer_iff]
      intro x
      constructor
      · exact hMEn m (hMy hm) x
      · intro hx
        have h := hMEn m⁻¹ (inv_mem (hMy hm)) _ hx
        have e : m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x := by group
        rwa [e] at h
    have hS := hP.inf_of_le_normalizer inf_le_left hnorm
    have h2 : IsPGroup 2 ↥(M ⊓ Eg uJ 11) :=
      (IsPGroup.of_card (n := 11) (card_Eg_uJ hM)).to_le inf_le_right
    exact (hS.eq_of_le inf_le_right le_rfl h2).le.trans inf_le_left
  have hME4 : 4 ≤ Nat.card ↥(M ⊓ Eg uJ 11) := by
    by_cases hPE : P ≤ Eg uJ 11
    · exact hP4.trans (card_le_of_le (le_inf hP.le hPE))
    · obtain ⟨t, htP, htE⟩ := IsConcreteLE.not_le_iff_exists.mp hPE
      have htM : t ∈ M := hP.le htP
      have htH : t ∈ Hj := hCH t (hMy htM)
      have hle := card_le_card_inf_centralizer_mul (N := M ⊓ Eg uJ 11)
        (fun x hx y hy => Eg_comm hel hx hy) (fun e he => Hj_normalizes_Eg hM t htH e he)
        (fun e he => by
          refine mem_inf.mpr ⟨mul_mem (hMn e (hEy e he) t htM) (inv_mem htM), ?_⟩
          have h1 := Hj_normalizes_Eg hM t htH e⁻¹ (inv_mem he)
          have e1 : e * t * e⁻¹ * t⁻¹ = e * (t * e⁻¹ * t⁻¹) := by group
          rw [e1]
          exact mul_mem he h1)
      rw [card_Eg_uJ hM] at hle
      have h128 := card_Eg_inf_centralizer_le htH htE (hPsq t htP)
      have h2 : 2 ^ 11 ≤ 128 * Nat.card ↥(M ⊓ Eg uJ 11) :=
        hle.trans (Nat.mul_le_mul_right _ h128)
      have h3 : (2 : ℕ) ^ 11 = 2048 := by norm_num
      omega
  have hy1 : eta uJ 11 1 ≠ 1 := eta_ne_one hM (by norm_num) (by norm_num)
  have hy2 : eta uJ 11 1 * eta uJ 11 1 = 1 := Eg_sq hel (eta_mem_Eg 11 le_rfl 1)
  have hnot : ¬ M ⊓ Eg uJ 11 ≤ zpowers (eta uJ 11 1) := by
    intro hle
    have h1 := card_le_of_le hle
    have hord : orderOf (eta uJ 11 1) = 2 := orderOf_eq_prime (by rw [sq]; exact hy2) hy1
    rw [Nat.card_zpowers, hord] at h1
    omega
  obtain ⟨m, hmME, hmz⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  obtain ⟨v, hv, rfl⟩ := (mem_Eg_iff hel).1 (mem_inf.mp hmME).2
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hmz (by rw [eta_zero]; exact one_mem _)
  have hv1 : v ≠ 1 := by
    rintro rfl
    exact hmz (mem_zpowers _)
  have hvlt : v < 2048 := lt_of_lt_of_le hv (by norm_num)
  have h2A : ∀ c ∈ zMasks, eta uJ 11 c ∈ M ⊓ Eg uJ 11 → False := by
    intro c hc hcME
    obtain ⟨g, -, hg⟩ := exists_conj_eta_three hM hc
    exact hP2A _ (hMEP hcME) g hg
  rcases mask_cover v hvlt with h0 | hT | hZ
  · exact hv0 h0
  · obtain ⟨w, -, hlet, hw1, hwz⟩ := c2_facts hT hv1
    have hconj := fun d => word_conj XJ act w (fun l hl d => hX_all hM (hlet l hl) d) d
    have hw1' : w.foldr act 1 = 1 := hw1
    have hwz' : v ^^^ w.foldr act v ∈ zMasks := hwz
    have hcy : (w.map XJ).prod ∈ centralizer ({eta uJ 11 1} : Set J) := by
      rw [mem_centralizer_singleton_iff]
      have h1 := hconj 1
      rw [hw1'] at h1
      calc (w.map XJ).prod * eta uJ 11 1
          = ((w.map XJ).prod * eta uJ 11 1 * ((w.map XJ).prod)⁻¹) * (w.map XJ).prod := by group
        _ = eta uJ 11 1 * (w.map XJ).prod := by rw [h1]
    have hmem := hMEn _ hcy _ hmME
    rw [hconj v] at hmem
    have hprod := mul_mem hmME hmem
    rw [← eta_xor hel le_rfl] at hprod
    exact h2A _ hwz' hprod
  · exact h2A v hZ hmME

end CFSG.ComponentClassification.RankTwoSporadic.J4Fink
