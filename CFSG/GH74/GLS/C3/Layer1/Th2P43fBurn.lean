module

public import CFSG.GH74.GLS.C3.Layer1.Th2P43fCaseB
public import CFSG.GH74.GLS.C3.Layer2.L5C7
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.GH74.GLS.Th2.P43f

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.Bk
  CFSG.GH74.GLS.C3.Layer1.Back CFSG.GH74.GLS.Th2 Equiv Equiv.Perm
  CFSG.LieType.SteinbergBR.SmallAlt

variable {G : Type} [Group G]

omit [Group G] in
theorem subgroup_le_or_le_of_forall {G : Type} [Group G] {H V V' : Subgroup G}
    (h : ∀ y ∈ H, y ∈ V ∨ y ∈ V') : H ≤ V ∨ H ≤ V' := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  obtain ⟨y₁, hy₁H, hy₁V⟩ := IsConcreteLE.not_le_iff_exists.1 h1
  obtain ⟨y₂, hy₂H, hy₂V'⟩ := IsConcreteLE.not_le_iff_exists.1 h2
  have hy₁V' : y₁ ∈ V' := (h y₁ hy₁H).resolve_left hy₁V
  have hy₂V : y₂ ∈ V := (h y₂ hy₂H).resolve_right hy₂V'
  rcases h (y₁ * y₂) (H.mul_mem hy₁H hy₂H) with hV | hV'
  · apply hy₁V
    have := V.mul_mem hV (V.inv_mem hy₂V)
    simpa using this
  · apply hy₂V'
    have := V'.mul_mem (V'.inv_mem hy₁V') hV'
    simpa using this

theorem dichotomy_perm {g g' τ : Perm (Fin 7)} (hg : g = a7P 2 ∨ g = a7P 3)
    (hg' : g' = a7P 6 ∨ g' = a7P 7) (hτ : τ = swap 5 6 ∨ τ = a7P 1 * swap 5 6) :
    (g * τ).support.card = τ.support.card ∨ (g' * τ).support.card = τ.support.card := by
  rcases hg with rfl | rfl <;> rcases hg' with rfl | rfl
  · exact a7P_dichotomy (Or.inl rfl) (Or.inl rfl) hτ
  · exact a7P_dichotomy (Or.inl rfl) (Or.inr rfl) hτ
  · exact a7P_dichotomy (Or.inr rfl) (Or.inl rfl) hτ
  · exact a7P_dichotomy (Or.inr rfl) (Or.inr rfl) hτ

theorem isConj_conj_of {x t : G} (h : IsConj x t) (g : G) : IsConj x (g * t * g⁻¹) :=
  h.trans (isConj_iff.2 ⟨g, rfl⟩)

variable {x : G} {K T S : Subgroup G} {a z : G} {psi : G → Perm (Fin 7)}

namespace Frame

variable (F : Frame x K T S a z psi)

include F

theorem B_props [Finite G] {D : Subgroup G} (hD : IsFourSub (T ⊓ K) D) :
    D ⊔ conjugate D a ≤ T ∧ CFSG.IsElementaryAbelian 2 ↥(D ⊔ conjugate D a) ∧
      Nat.card ↥(D ⊔ conjugate D a) = 16 := by
  have hDaP : conjugate D a ≤ conjugate (T ⊓ K) a := conjugate_le_conjugate' hD.1 a
  have hcomm : ∀ d ∈ D, ∀ d' ∈ conjugate D a, d * d' = d' * d := fun d hd d' hd' =>
    F.core.comm_P_conj d (hD.1 hd) d' (hDaP hd')
  have hdisj : D ⊓ conjugate D a = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have : y ∈ (T ⊓ K) ⊓ conjugate (T ⊓ K) a := ⟨hD.1 hy.1, hDaP hy.2⟩
    rw [F.core.P_inf_conj] at this
    exact this
  refine ⟨sup_le (hD.1.trans inf_le_left) ((hDaP.trans (F.core.conj_le F.core.P_le))),
    isElementaryAbelian_sup_of_commute hD.2.1 (isElementaryAbelian_conjugate hD.2.1 a) hcomm, ?_⟩
  rw [card_sup_of_commute_of_disjoint hcomm hdisj, card_conjugate', hD.2.2]

theorem R_four [Finite G] (hG : C3Hyp G) {y : G} (hs : Th2Std x y K T S)
    (e7 : kBar K ≃* alternatingGroup (Fin 7)) (hP2 : 2 ≤ pRank 2 ↥(T ⊓ K))
    (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4) :
    IsFourSub (T ⊓ K) (conjugate (T ⊓ CxK x K) a⁻¹) := by
  have hQP' := F.Q_le_conj hG hs e7 hP2 hQ4
  refine ⟨?_, isElementaryAbelian_conjugate F.Q_el a⁻¹, by rw [card_conjugate', hQ4]⟩
  intro r hr
  rw [mem_conjugate_iff'] at hr
  have := mem_conjugate_iff'.1 (hQP' hr)
  have e : a * (a⁻¹ * r * a⁻¹⁻¹) * a⁻¹ = r := by group
  rwa [e] at this

omit F in
theorem mem_R_iff {r : G} : r ∈ conjugate (T ⊓ CxK x K) a⁻¹ ↔ a⁻¹ * r * a ∈ T ⊓ CxK x K := by
  rw [mem_conjugate_iff']
  simp

theorem psi_R [Finite G] {r : G} (hr : r ∈ conjugate (T ⊓ CxK x K) a⁻¹) : psi (a⁻¹ * r * a) = 1 := by
  have h := mem_R_iff.1 hr
  exact (F.psi_ker _ (F.T_le_C h.1)).2 h.2

theorem mem_R_of_psi [Finite G] {s : G} (hs : s ∈ T ⊓ K) (h : psi (a⁻¹ * s * a) = 1) :
    s ∈ conjugate (T ⊓ CxK x K) a⁻¹ := by
  have hT := F.T_le_C (conj_mem_T F hs)
  exact mem_R_iff.2 ⟨F.core.a_inv_norm hs.1, (F.psi_ker _ hT).1 h⟩

theorem mixed_conj_v [Finite G] {D R V V₂ : Subgroup G} (hD : IsFourSub (T ⊓ K) D)
    (hR : IsFourSub (T ⊓ K) R) (hRd : R = conjugate (T ⊓ CxK x K) a⁻¹) (hRD : R ≠ D)
    (hV : IsFourSub (T ⊓ K) V) (hV₂ : IsFourSub (T ⊓ K) V₂) (hne : V ≠ D ∨ V₂ ≠ D) {u w : G}
    (hu : u ∈ V) (hw : w ∈ V₂) (hu1 : u ≠ 1) (hw1 : w ≠ 1) :
    IsConj (tt a u w) (z * x) := by
  have huP : u ∈ T ⊓ K := hV.1 hu
  have hwP : w ∈ T ⊓ K := hV₂.1 hw
  have hu2 : u * u = 1 := (forall_of_isElementaryAbelian hV.2.1).2 u hu
  have hw2 : w * w = 1 := (forall_of_isElementaryAbelian hV₂.2.1).2 w hw
  by_cases hV₂D : V₂ = D
  · have hVD : V ≠ D := hne.resolve_right (fun h => h hV₂D)
    have hVR : V = R := F.klein_unique_other hV hD hR hVD hRD
    have huR : u ∈ R := hVR ▸ hu
    exact F.isConj_tt_v_of_left huP hwP hu2 hw2 hu1 hw1 (F.psi_R (hRd ▸ huR))
  · have hV₂R : V₂ = R := F.klein_unique_other hV₂ hD hR hV₂D hRD
    have hwR : w ∈ R := hV₂R ▸ hw
    exact F.isConj_tt_v_of_right huP hwP hu2 hw2 hu1 hw1 (F.psi_R (hRd ▸ hwR))

theorem exists_mixed_x [Finite G] (hG : C3Hyp G) {y : G} (hs : Th2Std x y K T S)
    (e7 : kBar K ≃* alternatingGroup (Fin 7)) (hP2 : 2 ≤ pRank 2 ↥(T ⊓ K))
    (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4) {D R : Subgroup G} (hD : IsFourSub (T ⊓ K) D)
    (hR : IsFourSub (T ⊓ K) R) (hRd : R = conjugate (T ⊓ CxK x K) a⁻¹) (hRD : R ≠ D) :
    ∃ s ∈ D, s ≠ 1 ∧ s ≠ z ∧ IsConj (tt a s s) x := by
  obtain ⟨s, hsD, hs1, hsz⟩ := F.exists_nc hD
  obtain ⟨r, hrR, hr1, hrz⟩ := F.exists_nc hR
  have hsP : s ∈ T ⊓ K := hD.1 hsD
  have hrP : r ∈ T ⊓ K := hR.1 hrR
  have hs2 : s * s = 1 := (forall_of_isElementaryAbelian hD.2.1).2 s hsD
  have hr2 : r * r = 1 := (forall_of_isElementaryAbelian hR.2.1).2 r hrR
  have hsC : a⁻¹ * s * a ∈ conjugate (T ⊓ K) a := conj_mem_conj hsP
  have hsCC : a⁻¹ * s * a ∈ centralizer ({x} : Set G) := F.T_le_C (F.conj_mem_T hsP)
  have hτcomm : ∀ i : Fin 8, psi (a⁻¹ * s * a) * a7P i = a7P i * psi (a⁻¹ * s * a) := by
    intro i
    obtain ⟨u', hu', hui⟩ := F.psi_P_surj i
    rw [← hui, ← F.psi_mul _ hsCC u' (F.P_le_C hu'), ← F.psi_mul u' (F.P_le_C hu') _ hsCC]
    exact congrArg psi (F.core.comm_P_conj u' hu' _ hsC).symm
  have hτ : psi (a⁻¹ * s * a) = swap 5 6 ∨ psi (a⁻¹ * s * a) = a7P 1 * swap 5 6 := by
    rcases cent_a7P _ hτcomm with h1 | h1 | h1 | h1
    · exfalso
      have hsR : s ∈ R := hRd ▸ F.mem_R_of_psi hsP h1
      exact hRD (F.four_eq_of_nc hD hR hsD hs1 hsz hsR hs1 hsz (Or.inl rfl))
    · exfalso
      have hzq : z * (a⁻¹ * s * a) ∈ T ⊓ CxK x K := by
        have hT : z * (a⁻¹ * s * a) ∈ T := T.mul_mem F.z_mem.1 (F.conj_mem_T hsP)
        refine ⟨hT, (F.psi_ker _ (F.T_le_C hT)).1 ?_⟩
        rw [F.psi_mul z (F.P_le_C F.z_mem) _ hsCC, F.psi_z, h1]
        decide
      have hzP' : z * (a⁻¹ * s * a) ∈ conjugate (T ⊓ K) a := F.Q_le_conj hG hs e7 hP2 hQ4 hzq
      have hz' : z ∈ conjugate (T ⊓ K) a := by
        have := Subgroup.mul_mem _ hzP' (Subgroup.inv_mem _ hsC)
        have e : z * (a⁻¹ * s * a) * (a⁻¹ * s * a)⁻¹ = z := by group
        rwa [e] at this
      have : z ∈ (T ⊓ K) ⊓ conjugate (T ⊓ K) a := ⟨F.z_mem, hz'⟩
      rw [F.core.P_inf_conj, Subgroup.mem_bot] at this
      exact F.z_ne this
    · exact Or.inl h1
    · exact Or.inr h1
  have hsides := F.klein_sides hD hR hRD.symm hsD hs1 hsz hrR hr1 hrz
  have hdich : (psi s * psi (a⁻¹ * s * a)).support.card = (psi (a⁻¹ * s * a)).support.card ∨
      (psi r * psi (a⁻¹ * s * a)).support.card = (psi (a⁻¹ * s * a)).support.card := by
    rcases hsides with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact dichotomy_perm h1 h2 hτ
    · exact (dichotomy_perm h2 h1 hτ).symm
  have h1P : (1 : G) ∈ T ⊓ K := one_mem _
  have hone : (1 : G) * 1 = 1 := mul_one 1
  have hsx : IsConj (a⁻¹ * s * a) x := F.isConj_conj_x hsP hs2 hs1
  have ht1 : tt a 1 s = a⁻¹ * s * a := by unfold tt; rw [one_mul]
  rcases hdich with hA | hB
  · refine ⟨s, hsD, hs1, hsz, ?_⟩
    have := F.k_rule' hsP h1P hsP hs2 hone hs2 (by rw [F.psi_one, one_mul]; exact hA)
    rw [ht1] at this
    exact this.trans hsx
  · exfalso
    have h1 := F.k_rule' hrP h1P hsP hr2 hone hs2 (by rw [F.psi_one, one_mul]; exact hB)
    rw [ht1] at h1
    have h2 := F.isConj_tt_v_of_left hrP hsP hr2 hs2 hr1 hs1 (F.psi_R (hRd ▸ hrR))
    exact F.not_isConj_v_of_Q hG hs e7 hP2 hQ4 ⟨F.x_mem_T, F.x_mem_CxK⟩ F.x_sq F.x_ne
      (((h1.trans hsx).symm).trans h2)

theorem weakly_closed [Finite G] (hG : C3Hyp G) {y : G} (hs : Th2Std x y K T S)
    (e7 : kBar K ≃* alternatingGroup (Fin 7)) (hP2 : 2 ≤ pRank 2 ↥(T ⊓ K))
    (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4) {D R : Subgroup G} (hD : IsFourSub (T ⊓ K) D)
    (hR : IsFourSub (T ⊓ K) R) (hRd : R = conjugate (T ⊓ CxK x K) a⁻¹) (hRD : R ≠ D) :
    ∀ g : G, (D ⊔ conjugate D a).map (MulAut.conj g).toMonoidHom ≤ S →
      (D ⊔ conjugate D a).map (MulAut.conj g).toMonoidHom = D ⊔ conjugate D a := by
  intro g hgS
  obtain ⟨hBT, hBel, hB16⟩ := F.B_props hD
  set B : Subgroup G := D ⊔ conjugate D a with hB
  set E : Subgroup G := B.map (MulAut.conj g).toMonoidHom with hE
  have hEconj : E = conjugate B g⁻¹ := by
    rw [hE]
    unfold conjugate
    simp only [inv_inv]
  have hEel : CFSG.IsElementaryAbelian 2 ↥E := hEconj ▸ isElementaryAbelian_conjugate hBel g⁻¹
  have hE16 : Nat.card ↥E = 16 := by rw [hEconj, card_conjugate', hB16]
  have hET : E ≤ T := F.core.le_T_of_elementary F.T_eq (fun n hn _ => F.S_cases n hn)
    (fun e he => ⟨hgS he, F.S_le_normalizer_T e (hgS he)⟩) hEel (by omega)
  obtain ⟨V, V₂, hV, hV₂, hEVV⟩ := F.E24 hET hEel hE16
  by_contra hEB
  have hne : V ≠ D ∨ V₂ ≠ D := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    apply hEB
    rw [hEVV, hcon.1, hcon.2]
  have hxv := F.not_isConj_v_of_Q hG hs e7 hP2 hQ4 ⟨F.x_mem_T, F.x_mem_CxK⟩ F.x_sq F.x_ne
  have hV₂P : conjugate V₂ a ≤ conjugate (T ⊓ K) a := conjugate_le_conjugate' hV₂.1 a
  have hcommVV : ∀ u ∈ V, ∀ q ∈ conjugate V₂ a, u * q = q * u := fun u hu q hq =>
    F.core.comm_P_conj u (hV.1 hu) q (hV₂P hq)
  have hxcl : ∀ e ∈ E, IsConj x e → e ∈ V ∨ e ∈ conjugate V₂ a := by
    intro e heE hxe
    have he' : e ∈ V ⊔ conjugate V₂ a := hEVV ▸ heE
    obtain ⟨u, hu, q, hq, rfl⟩ :=
      CFSG.GH74.GLS.C3.Layer1.Bk.mem_sup_of_commute hcommVV he'
    by_cases hu1 : u = 1
    · right
      rw [hu1, one_mul]
      exact hq
    by_cases hw1 : a * q * a⁻¹ = 1
    · left
      have hq1 : q = 1 := by
        calc q = a⁻¹ * (a * q * a⁻¹) * a := by group
          _ = 1 := by rw [hw1]; group
      rw [hq1, mul_one]
      exact hu
    · exfalso
      have hwV₂ : a * q * a⁻¹ ∈ V₂ := mem_conjugate_iff'.1 hq
      have hmix := F.mixed_conj_v hD hR hRd hRD hV hV₂ hne hu hwV₂ hu1 hw1
      have e : tt a u (a * q * a⁻¹) = u * q := by
        unfold tt
        congr 1
        group
      rw [e] at hmix
      exact hxv (hxe.trans hmix)
  set D₁ : Subgroup G := D.map (MulAut.conj g).toMonoidHom with hD₁
  set D₂ : Subgroup G := (conjugate D a).map (MulAut.conj g).toMonoidHom with hD₂
  have hD₁E : D₁ ≤ E := Subgroup.map_mono le_sup_left
  have hD₂E : D₂ ≤ E := Subgroup.map_mono le_sup_right
  have hEsup : E = D₁ ⊔ D₂ := by rw [hE, hB, Subgroup.map_sup]
  have hD₁x : ∀ e ∈ D₁, e = 1 ∨ IsConj x e := by
    rintro _ ⟨d, hd, rfl⟩
    by_cases hd1 : d = 1
    · left
      rw [hd1]
      simp [MulAut.conj_apply]
    · right
      have hdx : IsConj x d := (F.isConj_P_x (hD.1 hd) ((forall_of_isElementaryAbelian hD.2.1).2 d hd)
        hd1).symm
      simpa [MulAut.conj_apply] using isConj_conj_of hdx g
  have hD₂x : ∀ e ∈ D₂, e = 1 ∨ IsConj x e := by
    rintro _ ⟨q, hq, rfl⟩
    by_cases hq1 : q = 1
    · left
      rw [hq1]
      simp [MulAut.conj_apply]
    · right
      have hwD : a * q * a⁻¹ ∈ D := mem_conjugate_iff'.1 hq
      have hw1 : a * q * a⁻¹ ≠ 1 := by
        intro h
        apply hq1
        calc q = a⁻¹ * (a * q * a⁻¹) * a := by group
          _ = 1 := by rw [h]; group
      have hqx : IsConj x q := by
        have := (F.isConj_conj_x (hD.1 hwD) ((forall_of_isElementaryAbelian hD.2.1).2 _ hwD) hw1).symm
        have e : a⁻¹ * (a * q * a⁻¹) * a = q := by group
        rwa [e] at this
      simpa [MulAut.conj_apply] using isConj_conj_of hqx g
  have hD₁V : D₁ ≤ V ∨ D₁ ≤ conjugate V₂ a := by
    refine subgroup_le_or_le_of_forall (fun e he => ?_)
    rcases hD₁x e he with h1 | h1
    · left
      rw [h1]
      exact one_mem _
    · exact hxcl e (hD₁E he) h1
  have hD₂V : D₂ ≤ V ∨ D₂ ≤ conjugate V₂ a := by
    refine subgroup_le_or_le_of_forall (fun e he => ?_)
    rcases hD₂x e he with h1 | h1
    · left
      rw [h1]
      exact one_mem _
    · exact hxcl e (hD₂E he) h1
  obtain ⟨s, hsD, hs1, hsz, hsx⟩ := F.exists_mixed_x hG hs e7 hP2 hQ4 hD hR hRd hRD
  have hsq : a⁻¹ * s * a ∈ conjugate D a := C3.Layer1.Bk.Sec4Core.mem_conj_of D hsD
  set e₁ : G := g * s * g⁻¹ with he₁
  set e₂ : G := g * (a⁻¹ * s * a) * g⁻¹ with he₂
  have he₁D : e₁ ∈ D₁ := ⟨s, hsD, by simp [MulAut.conj_apply, he₁]⟩
  have he₂D : e₂ ∈ D₂ := ⟨_, hsq, by simp [MulAut.conj_apply, he₂]⟩
  have hs1' : e₁ ≠ 1 := by
    intro h
    apply hs1
    calc s = g⁻¹ * (g * s * g⁻¹) * g := by group
      _ = 1 := by rw [← he₁, h]; group
  have hsq1 : a⁻¹ * s * a ≠ 1 := by
    intro h
    apply hs1
    calc s = a * (a⁻¹ * s * a) * a⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hs2' : e₂ ≠ 1 := by
    intro h
    apply hsq1
    calc a⁻¹ * s * a = g⁻¹ * (g * (a⁻¹ * s * a) * g⁻¹) * g := by group
      _ = 1 := by rw [← he₂, h]; group
  have hmx : IsConj x (e₁ * e₂) := by
    have := isConj_conj_of hsx.symm g
    have e : g * tt a s s * g⁻¹ = e₁ * e₂ := by
      unfold tt
      rw [he₁, he₂]
      group
    rwa [e] at this
  have hE16' : ∀ W : Subgroup G, Nat.card ↥W = 4 → E ≤ W → False := by
    intro W hW hEW
    have := Subgroup.card_le_of_le hEW
    omega
  have hVc : Nat.card ↥V = 4 := hV.2.2
  have hV₂c : Nat.card ↥(conjugate V₂ a) = 4 := by rw [card_conjugate', hV₂.2.2]
  rcases hD₁V with h1 | h1 <;> rcases hD₂V with h2 | h2
  · exact hE16' V hVc (by rw [hEsup]; exact sup_le h1 h2)
  ·
    have hwV₂ : a * e₂ * a⁻¹ ∈ V₂ := mem_conjugate_iff'.1 (h2 he₂D)
    have hmix := F.mixed_conj_v hD hR hRd hRD hV hV₂ hne (h1 he₁D) hwV₂ hs1' (by
      intro h
      apply hs2'
      calc e₂ = a⁻¹ * (a * e₂ * a⁻¹) * a := by group
        _ = 1 := by rw [h]; group)
    have e : tt a e₁ (a * e₂ * a⁻¹) = e₁ * e₂ := by
      unfold tt
      congr 1
      group
    rw [e] at hmix
    exact hxv (hmx.trans hmix)
  ·
    have hwV₂ : a * e₁ * a⁻¹ ∈ V₂ := mem_conjugate_iff'.1 (h1 he₁D)
    have hmix := F.mixed_conj_v hD hR hRd hRD hV hV₂ hne (h2 he₂D) hwV₂ hs2' (by
      intro h
      apply hs1'
      calc e₁ = a⁻¹ * (a * e₁ * a⁻¹) * a := by group
        _ = 1 := by rw [h]; group)
    have e : tt a e₂ (a * e₁ * a⁻¹) = e₁ * e₂ := by
      unfold tt
      calc e₂ * (a⁻¹ * (a * e₁ * a⁻¹) * a) = e₂ * e₁ := by group
        _ = e₁ * e₂ := (hcommVV e₂ (h2 he₂D) e₁ (h1 he₁D))
    rw [e] at hmix
    exact hxv (hmx.trans hmix)
  · exact hE16' (conjugate V₂ a) hV₂c (by rw [hEsup]; exact sup_le h1 h2)

theorem fuses_case_a [Finite G] (hG : C3Hyp G) {y : G} (hs : Th2Std x y K T S)
    (e7 : kBar K ≃* alternatingGroup (Fin 7)) (hP2 : 2 ≤ pRank 2 ↥(T ⊓ K))
    (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4) {D R : Subgroup G} (hD : IsFourSub (T ⊓ K) D)
    (hR : IsFourSub (T ⊓ K) R) (hRd : R = conjugate (T ⊓ CxK x K) a⁻¹) (hRD : R ≠ D) :
    FusesIn x (D ⊔ conjugate D a) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro b hbB ⟨c, hc⟩
  obtain ⟨hBT, hBel, -⟩ := F.B_props hD
  have hSyl : Stage1.Thm6.IsSylow2In S ⊤ := (isSylowOf_iff (p := 2)).1 hs.sylowS
  have hBS : D ⊔ conjugate D a ≤ S := hBT.trans F.core.T_le_S
  have hxB : x ∈ D ⊔ conjugate D a := by
    refine Subgroup.mem_sup_right ?_
    rw [mem_conjugate_iff', F.a_x]
    exact F.z_mem_four hD
  obtain ⟨n, hn, hnx⟩ := C3.Layer2.L5.burnside_weak S (D ⊔ conjugate D a) F.core.S_pgroup hSyl hBS
    (forall_of_isElementaryAbelian hBel).1
    (F.weakly_closed hG hs e7 hP2 hQ4 hD hR hRd hRD) x hxB c⁻¹ (by simpa using hc ▸ hbB)
  refine ⟨n⁻¹, Subgroup.inv_mem _ hn, ?_⟩
  rw [inv_inv, hnx, ← hc]
  group

end Frame

end CFSG.GH74.GLS.Th2.P43f
