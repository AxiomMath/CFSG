module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitTheta

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_conj_eq_of_mem_normalizer {H : Subgroup G} {x : G}
    (hx : x ∈ normalizer (H : Set G)) : H.map (MulAut.conj x).toMonoidHom = H := by
  ext y
  rw [mem_map_equiv, MulAut.conj_symm_apply]
  have h := (mem_normalizer_iff.mp (inv_mem hx)) y
  rw [inv_inv] at h
  exact h.symm

theorem mem_normalizer_of_map_conj_le {H : Subgroup G} {x : G}
    (h : H.map (MulAut.conj x).toMonoidHom ≤ H) : x ∈ normalizer (H : Set G) :=
  mem_normalizer_of_map_conj_eq (Subgroup.eq_of_le_of_card_ge h
    (by rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]))

theorem le_commutator_sup_inf_centralizer {P X : Subgroup G} (hP : IsPGroup 2 P)
    (hPX : P ≤ normalizer (X : Set G)) (hX : Odd (Nat.card X)) :
    X ≤ ⁅X, P⁆ ⊔ (X ⊓ centralizer (P : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCX : ⁅X, P⁆ ≤ X := commutator_le_self_of_le_normalizer hPX
  have hCodd : ¬ 2 ∣ Nat.card ↥(⁅X, P⁆ : Subgroup G) := fun h2 =>
    (Nat.not_even_iff_odd.mpr (Odd.of_dvd_nat hX (card_dvd_of_le hCX))) (even_iff_two_dvd.mpr h2)
  have hPC : P ≤ normalizer ((⁅X, P⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator_of_le_normalizers hPX le_normalizer
  intro y hy
  obtain ⟨n, hn, hyn⟩ := exists_mul_mem_centralizer hP hCodd hPC (y := y) fun u hu => by
    have h1 : y⁻¹ * (u * y * u⁻¹) = ⁅y⁻¹, u⁆ := by rw [commutatorElement_def, inv_inv]; group
    rw [h1]
    exact commutator_mem_commutator (inv_mem hy) hu
  have hy' : y = (y * n) * n⁻¹ := by group
  rw [hy']
  exact mul_mem (mem_sup_right (mem_inf.mpr ⟨mul_mem hy (hCX hn), hyn⟩))
    (mem_sup_left (inv_mem hn))

omit [Finite G] in
theorem isKleinFour_of_card_four_of_sq {H : Type*} [Group H] (h4 : Nat.card H = 4)
    (hsq : ∀ x : H, x ^ 2 = 1) : IsKleinFour H := by
  refine ⟨h4, ?_⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp (Monoid.exponent_dvd_of_forall_pow_eq_one hsq) with
    h | h
  · have : Subsingleton H := Monoid.exp_eq_one_iff.mp h
    have := Nat.card_of_subsingleton (1 : H)
    omega
  · exact h

theorem oddCoreOfCentralizer_le_normalizer {E V : Subgroup G} (hEc : IsMulCommutative E)
    (hexp : ∀ e ∈ E, e ^ 2 = 1) (h8 : Nat.card E = 8) (hV : IsKleinFour V)
    (hVE : ∀ e ∈ E, e ∈ centralizer (V : Set G))
    (hbal : ∀ a ∈ E, a ≠ 1 → ∀ b ∈ E, b ≠ 1 →
      footeTheta V a ⊓ centralizer ({b} : Set G) ≤ footeTheta V b)
    {b : G} (hb : b ∈ E) (hb1 : b ≠ 1) :
    oddCoreOfCentralizer b ≤
      normalizer ((⨆ a ∈ E, ⨆ (_ : a ≠ 1), footeTheta V a : Subgroup G) : Set G) := by
  have h8' : 2 ^ 3 ∣ Nat.card E := by rw [h8]; norm_num
  have hcomm : ∀ x ∈ E, ∀ a ∈ E, x * a = a * x := fun x hx a ha =>
    congrArg Subtype.val (isMulCommutative_iff.mp hEc ⟨x, hx⟩ ⟨a, ha⟩)
  have hVb : V ≤ centralizer ({b} : Set G) := fun v hv =>
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hVE b hb)) v hv)
  have hVO : V ≤ normalizer ((oddCoreOfCentralizer b : Subgroup G) : Set G) := fun _ hv =>
    mem_normalizer_oddCoreOfCentralizer (hVb hv)
  have hVp : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hV.card_four]; norm_num)
  refine (le_commutator_sup_inf_centralizer hVp hVO (odd_card_oddCoreOfCentralizer b)).trans
    (sup_le ?_ ?_)
  · have h1 : ⁅oddCoreOfCentralizer b, V⁆ ≤ footeTheta V b := le_sup_left
    exact (h1.trans (footeTheta_le_iSup hb hb1)).trans le_normalizer
  · have hE1 : E ≠ ⊥ := fun h => by rw [h, card_bot] at h8; omega
    have hEY : E ≤ normalizer
        ((oddCoreOfCentralizer b ⊓ centralizer (V : Set G) : Subgroup G) : Set G) :=
      fun e he => mem_normalizer_inf' (mem_normalizer_oddCoreOfCentralizer
        (mem_centralizer_singleton_iff.mpr (hcomm e he b hb))) (le_normalizer (hVE e he))
    have hodd : Odd (Nat.card ↥(oddCoreOfCentralizer b ⊓ centralizer (V : Set G))) :=
      Odd.of_dvd_nat (odd_card_oddCoreOfCentralizer b) (card_dvd_of_le inf_le_left)
    refine le_of_forall_hyperplane_inf_centralizer_le hEc hexp hE1 hEY hodd fun B hBE hBcard => ?_
    have hB4 : Nat.card B = 4 := by omega
    have hBK : IsKleinFour B := isKleinFour_of_card_four_of_sq hB4 fun x =>
      Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hexp x (hBE x.2))
    rw [footeTheta_completion_eq_iSup hEc hexp h8' hVE hbal hBK hBE]
    intro g hg
    obtain ⟨⟨-, hgV⟩, hgB⟩ := mem_inf.mp hg |>.imp_left mem_inf.mp
    apply mem_normalizer_of_map_conj_eq
    simp only [Subgroup.map_iSup]
    refine iSup_congr fun w => iSup_congr fun hw => iSup_congr fun _ =>
      map_conj_footeTheta ?_ hgV
    exact ((mem_centralizer_iff.mp hgB) w hw).symm

theorem le_oddCoreIn_iSup {E V : Subgroup G} (hEc : IsMulCommutative E)
    (hexp : ∀ e ∈ E, e ^ 2 = 1) (h8 : Nat.card E = 8) (hV : IsKleinFour V)
    (hVE : ∀ e ∈ E, e ∈ centralizer (V : Set G))
    (hbal : ∀ a ∈ E, a ≠ 1 → ∀ b ∈ E, b ≠ 1 →
      footeTheta V a ⊓ centralizer ({b} : Set G) ≤ footeTheta V b) :
    (⨆ a ∈ E, ⨆ (_ : a ≠ 1), footeTheta V a) ≤
      oddCoreIn (⨆ b ∈ E, ⨆ (_ : b ≠ 1), oddCoreOfCentralizer b) := by
  have h8' : 2 ^ 3 ∣ Nat.card E := by rw [h8]; norm_num
  have hVa : ∀ a ∈ E, V ≤ centralizer ({a} : Set G) := fun a ha v hv =>
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hVE a ha)) v hv)
  refine le_oddCoreIn ?_ ?_ (footeTheta_completion hEc hexp h8' hVE hbal).1
  · exact iSup₂_le fun a ha => iSup_le fun ha1 =>
      (footeTheta_le (hVa a ha)).trans (le_iSup₂_of_le
        (f := fun a (_ : a ∈ E) => ⨆ (_ : a ≠ 1), oddCoreOfCentralizer a) a ha
        (le_iSup (fun _ : a ≠ 1 => oddCoreOfCentralizer a) ha1))
  · exact iSup₂_le fun b hb => iSup_le fun hb1 =>
      oddCoreOfCentralizer_le_normalizer hEc hexp h8 hV hVE hbal hb hb1

omit [Finite G] in
theorem centralizer_le_normalizer_oddCoreIn_iSup {E : Subgroup G} :
    centralizer (E : Set G) ≤
      normalizer ((oddCoreIn (⨆ b ∈ E, ⨆ (_ : b ≠ 1), oddCoreOfCentralizer b) : Subgroup G) :
        Set G) := by
  intro g hg
  apply mem_normalizer_oddCoreIn
  apply mem_normalizer_of_map_conj_eq
  simp only [Subgroup.map_iSup]
  refine iSup_congr fun b => iSup_congr fun hb => iSup_congr fun _ => ?_
  have hgb : (MulAut.conj g) b = b := by
    rw [MulAut.conj_apply, ← (mem_centralizer_iff.mp hg) b hb, mul_assoc, mul_inv_cancel,
      mul_one]
  rw [map_oddCoreOfCentralizer_mulEquiv, hgb]

omit [Finite G] in
theorem mem_normalizer_sup {A B : Subgroup G} {y : G} (hA : y ∈ normalizer (A : Set G))
    (hB : y ∈ normalizer (B : Set G)) : y ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  apply mem_normalizer_of_map_conj_eq
  rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer hA, map_conj_eq_of_mem_normalizer hB]

theorem commutator_map_conj_le_oddCoreIn_iSup {E V : Subgroup G} (hEc : IsMulCommutative E)
    (hexp : ∀ e ∈ E, e ^ 2 = 1) (h8 : Nat.card E = 8) (hV : IsKleinFour V)
    (hVE : ∀ e ∈ E, e ∈ centralizer (V : Set G))
    (hbal : ∀ a ∈ E, a ≠ 1 → ∀ b ∈ E, b ≠ 1 →
      footeTheta V a ⊓ centralizer ({b} : Set G) ≤ footeTheta V b)
    {e g : G} (he : e ∈ E) (he1 : e ≠ 1) (hg : g ∈ centralizer (E : Set G)) :
    ⁅oddCoreOfCentralizer e, V.map (MulAut.conj g).toMonoidHom⁆ ≤
      oddCoreIn (⨆ b ∈ E, ⨆ (_ : b ≠ 1), oddCoreOfCentralizer b) := by
  have h0 : ⁅oddCoreOfCentralizer e, V⁆ ≤ footeTheta V e := le_sup_left
  have h1 := map_mono (f := (MulAut.conj g).toMonoidHom)
    ((h0.trans (footeTheta_le_iSup he he1)).trans (le_oddCoreIn_iSup hEc hexp h8 hV hVE hbal))
  have hge : (MulAut.conj g) e = e := by
    rw [MulAut.conj_apply, ← (mem_centralizer_iff.mp hg) e he, mul_assoc, mul_inv_cancel, mul_one]
  rwa [Subgroup.map_commutator, map_oddCoreOfCentralizer_mulEquiv, hge,
    map_conj_eq_of_mem_normalizer (centralizer_le_normalizer_oddCoreIn_iSup hg)] at h1

theorem commutator_le_oddCoreIn_iSup {E V L₀ W : Subgroup G} (hEc : IsMulCommutative E)
    (hexp : ∀ e ∈ E, e ^ 2 = 1) (h8 : Nat.card E = 8) (hV : IsKleinFour V)
    (hVE : ∀ e ∈ E, e ∈ centralizer (V : Set G))
    (hbal : ∀ a ∈ E, a ≠ 1 → ∀ b ∈ E, b ≠ 1 →
      footeTheta V a ⊓ centralizer ({b} : Set G) ≤ footeTheta V b)
    (hL₀E : L₀ ≤ centralizer (E : Set G)) (hWE : W ≤ centralizer (E : Set G))
    (hWL₀ : ∀ g ∈ W, V.map (MulAut.conj g).toMonoidHom ≤ L₀)
    (hL₀ : L₀ ≤ closure (⋃ g ∈ W, ((V.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)))
    {e : G} (he : e ∈ E) (he1 : e ≠ 1) :
    ⁅oddCoreOfCentralizer e, L₀⁆ ≤ oddCoreIn (⨆ b ∈ E, ⨆ (_ : b ≠ 1), oddCoreOfCentralizer b) := by
  set N := oddCoreIn (⨆ b ∈ E, ⨆ (_ : b ≠ 1), oddCoreOfCentralizer b) with hNdef
  have hN : ∀ y ∈ L₀, y ∈ normalizer (N : Set G) := fun y hy =>
    centralizer_le_normalizer_oddCoreIn_iSup (hL₀E hy)
  have hSL : closure (⋃ g ∈ W, ((V.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) ≤
      L₀ := by
    rw [closure_le]
    intro x hx
    simp only [Set.mem_iUnion, SetLike.mem_coe] at hx
    obtain ⟨g, hg, hxg⟩ := hx
    exact hWL₀ g hg hxg
  rw [commutator_le]
  intro q hq x hx
  refine closure_induction (p := fun x _ => ⁅q, x⁆ ∈ N) ?_ ?_ ?_ ?_ (hL₀ hx)
  · intro y hy
    simp only [Set.mem_iUnion, SetLike.mem_coe] at hy
    obtain ⟨g, hg, hyg⟩ := hy
    exact commutator_map_conj_le_oddCoreIn_iSup hEc hexp h8 hV hVE hbal he he1 (hWE hg)
      (commutator_mem_commutator hq hyg)
  · simp only [commutatorElement_def, mul_one, mul_inv_cancel]
    exact one_mem N
  · intro y z hy hz py pz
    have e1 : ⁅q, y * z⁆ = ⁅q, y⁆ * (y * ⁅q, z⁆ * y⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e1]
    exact mul_mem py ((mem_normalizer_iff.mp (hN y (hSL hy)) _).mp pz)
  · intro y hy py
    have e1 : ⁅q, y⁻¹⁆ = y⁻¹ * ⁅q, y⁆⁻¹ * y⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e1]
    exact (mem_normalizer_iff.mp (hN _ (L₀.inv_mem (hSL hy))) _).mp (inv_mem py)

theorem odd_card_iSup_oddCoreIn {E V L₀ W : Subgroup G} (hEc : IsMulCommutative E)
    (hexp : ∀ e ∈ E, e ^ 2 = 1) (h8 : Nat.card E = 8) (hV : IsKleinFour V)
    (hVE : ∀ e ∈ E, e ∈ centralizer (V : Set G))
    (hbal : ∀ a ∈ E, a ≠ 1 → ∀ b ∈ E, b ≠ 1 →
      footeTheta V a ⊓ centralizer ({b} : Set G) ≤ footeTheta V b)
    (hL₀E : L₀ ≤ centralizer (E : Set G)) (hWE : W ≤ centralizer (E : Set G))
    (hWL₀ : ∀ g ∈ W, V.map (MulAut.conj g).toMonoidHom ≤ L₀)
    (hL₀ : L₀ ≤ closure (⋃ g ∈ W, ((V.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)))
    (K : G → Subgroup G) (hK₀ : ∀ e ∈ E, e ≠ 1 → L₀ ≤ K e)
    (hKsup : ∀ e ∈ E, e ≠ 1 → K e ≤ L₀ ⊔ oddCoreIn (K e))
    (hKres : ∀ e ∈ E, e ≠ 1 → K e ≤ oddResidualIn (K e))
    (hKO : ∀ e ∈ E, e ≠ 1 → oddCoreIn (K e) ≤ oddCoreOfCentralizer e) :
    Odd (Nat.card ↥(⨆ e ∈ E, ⨆ (_ : e ≠ 1), oddCoreIn (K e))) := by
  set Dt := ⨆ b ∈ E, ⨆ (_ : b ≠ 1), oddCoreOfCentralizer b with hDt
  set N := oddCoreIn Dt with hNdef
  have hL₀N : L₀ ≤ normalizer (N : Set G) := hL₀E.trans centralizer_le_normalizer_oddCoreIn_iSup
  have hNodd : Odd (Nat.card N) := odd_card_oddCoreIn _
  have hDtN : Dt ≤ normalizer (N : Set G) := fun x hx =>
    mem_normalizer_oddCoreIn (le_normalizer hx)
  have hP : Odd (Nat.card ↥(oddCoreIn L₀ ⊔ N)) :=
    odd_card_sup_of_le_normalizer ((map_subtype_le _).trans hL₀N) (odd_card_oddCoreIn L₀) hNodd
  have hle : ∀ e ∈ E, e ≠ 1 → oddCoreIn (K e) ≤ oddCoreIn L₀ ⊔ N := by
    intro e he he1
    set Q := oddCoreIn (K e) with hQ
    have hQO := hKO e he he1
    have hQDt : Q ≤ Dt := hQO.trans (le_iSup₂_of_le
      (f := fun b (_ : b ∈ E) => ⨆ (_ : b ≠ 1), oddCoreOfCentralizer b) e he
      (le_iSup (fun _ : e ≠ 1 => oddCoreOfCentralizer e) he1))
    have hcomm := commutator_le_oddCoreIn_iSup hEc hexp h8 hV hVE hbal hL₀E hWE hWL₀ hL₀ he he1
    have hQR : Q ≤ normalizer ((L₀ ⊔ N : Subgroup G) : Set G) := fun q hq =>
      mem_normalizer_of_map_conj_le (by
        rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer (hDtN (hQDt hq))]
        refine sup_le ?_ le_sup_right
        rw [Subgroup.map_le_iff_le_comap]
        intro l hl
        show q * l * q⁻¹ ∈ L₀ ⊔ N
        have e1 : q * l * q⁻¹ = ⁅q, l⁆ * l := by rw [commutatorElement_def]; group
        rw [e1]
        exact mul_mem (mem_sup_right (hcomm (commutator_mem_commutator (hQO hq) hl)))
          (mem_sup_left hl))
    have hKR : K e ≤ L₀ ⊔ N := by
      refine (hKres e he he1).trans ((closure_le _).mpr fun g hg => ?_)
      obtain ⟨hgK, h2⟩ := hg
      have hg' : g ∈ Q ⊔ (L₀ ⊔ N) :=
        (sup_le (le_sup_left.trans le_sup_right) le_sup_left : L₀ ⊔ Q ≤ Q ⊔ (L₀ ⊔ N))
          (hKsup e he he1 hgK)
      exact mem_of_two_element_of_mem_sup hQR
        (by rw [oddResidualIn_eq_bot_of_odd (odd_card_oddCoreIn _)]; exact bot_le) hg' h2
    have hQNodd : Odd (Nat.card ↥(Q ⊔ N)) :=
      odd_card_sup_of_le_normalizer (hQDt.trans hDtN) (odd_card_oddCoreIn _) hNodd
    have hL₀QN : L₀ ⊓ (Q ⊔ N) ≤ oddCoreIn L₀ := le_oddCoreIn inf_le_left
      (fun y hy => mem_normalizer_inf' (le_normalizer hy) (mem_normalizer_sup
        (mem_normalizer_oddCoreIn (le_normalizer (hK₀ e he he1 hy))) (hL₀N hy)))
      (Odd.of_dvd_nat hQNodd (card_dvd_of_le inf_le_right))
    intro q hq
    have hqR : q ∈ L₀ ⊔ N := hKR (map_subtype_le _ hq)
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right L₀ N hL₀N] at hqR
    obtain ⟨l, hl, n, hn, rfl⟩ := hqR
    have hlQN : l ∈ Q ⊔ N := by
      have e1 : l = (l * n) * n⁻¹ := by group
      rw [e1]
      exact mul_mem (mem_sup_left hq) (mem_sup_right (inv_mem hn))
    exact mul_mem (mem_sup_left (hL₀QN (mem_inf.mpr ⟨hl, hlQN⟩))) (mem_sup_right hn)
  exact Odd.of_dvd_nat hP (card_dvd_of_le (iSup₂_le fun e he => iSup_le fun he1 => hle e he he1))

theorem le_sup_oddCoreIn_iSup {E V L₀ W : Subgroup G} (hEc : IsMulCommutative E)
    (hexp : ∀ e ∈ E, e ^ 2 = 1) (h8 : Nat.card E = 8) (hV : IsKleinFour V)
    (hVE : ∀ e ∈ E, e ∈ centralizer (V : Set G))
    (hbal : ∀ a ∈ E, a ≠ 1 → ∀ b ∈ E, b ≠ 1 →
      footeTheta V a ⊓ centralizer ({b} : Set G) ≤ footeTheta V b)
    (hL₀E : L₀ ≤ centralizer (E : Set G)) (hWE : W ≤ centralizer (E : Set G))
    (hWL₀ : ∀ g ∈ W, V.map (MulAut.conj g).toMonoidHom ≤ L₀)
    (hL₀ : L₀ ≤ closure (⋃ g ∈ W, ((V.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)))
    (K : G → Subgroup G) (hK₀ : ∀ e ∈ E, e ≠ 1 → L₀ ≤ K e)
    (hKsup : ∀ e ∈ E, e ≠ 1 → K e ≤ L₀ ⊔ oddCoreIn (K e))
    (hKres : ∀ e ∈ E, e ≠ 1 → K e ≤ oddResidualIn (K e))
    (hKO : ∀ e ∈ E, e ≠ 1 → oddCoreIn (K e) ≤ oddCoreOfCentralizer e) :
    (⨆ e ∈ E, ⨆ (_ : e ≠ 1), oddCoreIn (K e)) ≤ oddCoreIn (⨆ e ∈ E, ⨆ (_ : e ≠ 1), K e) ∧
      (⨆ e ∈ E, ⨆ (_ : e ≠ 1), K e) ≤ L₀ ⊔ oddCoreIn (⨆ e ∈ E, ⨆ (_ : e ≠ 1), K e) := by
  set X := ⨆ e ∈ E, ⨆ (_ : e ≠ 1), oddCoreIn (K e) with hX
  set M := ⨆ e ∈ E, ⨆ (_ : e ≠ 1), K e with hM
  have hXodd := odd_card_iSup_oddCoreIn hEc hexp h8 hV hVE hbal hL₀E hWE hWL₀ hL₀ K hK₀ hKsup
    hKres hKO
  have hXM : X ≤ M := iSup₂_le fun e he => iSup_le fun he1 => (map_subtype_le _).trans
    (le_iSup₂_of_le (f := fun e (_ : e ∈ E) => ⨆ (_ : e ≠ 1), K e) e he
      (le_iSup (fun _ : e ≠ 1 => K e) he1))
  have hMLX : M ≤ L₀ ⊔ X := iSup₂_le fun e he => iSup_le fun he1 => (hKsup e he he1).trans
    (sup_le_sup_left (le_iSup₂_of_le (f := fun e (_ : e ∈ E) => ⨆ (_ : e ≠ 1), oddCoreIn (K e))
      e he (le_iSup (fun _ : e ≠ 1 => oddCoreIn (K e)) he1)) _)
  have hL₀X : L₀ ≤ normalizer (X : Set G) := fun l hl => by
    apply mem_normalizer_of_map_conj_eq
    simp only [hX, Subgroup.map_iSup]
    exact iSup_congr fun e => iSup_congr fun he => iSup_congr fun he1 =>
      map_conj_eq_of_mem_normalizer (mem_normalizer_oddCoreIn (le_normalizer (hK₀ e he he1 hl)))
  have hMX : M ≤ normalizer (X : Set G) := hMLX.trans (sup_le hL₀X le_normalizer)
  have hXO : X ≤ oddCoreIn M := le_oddCoreIn hXM hMX hXodd
  exact ⟨hXO, hMLX.trans (sup_le_sup_left hXO _)⟩

end CFSG.ComponentClassification.FooteLit
