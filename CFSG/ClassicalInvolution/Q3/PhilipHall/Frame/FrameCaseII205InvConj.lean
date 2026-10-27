module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205Defs
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205I2
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205IQ8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf3HexMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
  CFSG.ClassicalInvolution.Balance.Bootstrap
open Out
open scoped commutatorElement


theorem frameAInvConj_holds : FrameAInvConj := by
  intro G _ _ _ K K' J S R R' W V z t d L s hL
  set X := sec20X (CoreAssembly.conjClass K) z K K' with hXdef
  have hKK'X : K ⊔ K' ≤ X := sup_le (le_sup_of_le_left le_sup_right) le_sup_right
  have hcomm : ∀ m ∈ X, z * m = m * z := fun m hm =>
    (Subgroup.mem_centralizer_singleton_iff.mp (sec20X_le_centralizer_z d hm)).symm
  have hconjz : ∀ m ∈ X, m⁻¹ * z * m = z := fun m hm => by
    calc m⁻¹ * z * m = m⁻¹ * (z * m) := by group
      _ = m⁻¹ * (m * z) := by rw [hcomm m hm]
      _ = z := by group
  obtain ⟨u, hu, h1, h4u, hu1⟩ : ∃ u ∈ X, u * u = s ∧ u ^ 4 = 1 ∧ u * u ≠ 1 := by
    rcases hL with ⟨zK, h⟩ | ⟨zK, h⟩
    · exact exists_sq_of_aviol d d.late_mem_K d.viol.hzK h
    · exact exists_sq_of_aviol d d.late_mem_K' d.late_hzK' h
  obtain ⟨hsmem, hsz⟩ : s ∈ K ⊔ K' ∧ s ≠ z := by
    rcases hL with ⟨zK, h⟩ | ⟨zK, h⟩
    · exact aviol_involution_mem d d.late_mem_K d.viol.hzK d.twins h
    · obtain ⟨h', h''⟩ := aviol_involution_mem d d.late_mem_K' d.late_hzK' (twinSet_K' d) h
      exact ⟨by rw [sup_comm]; exact h', h''⟩
  have huu2 : u * u * (u * u) = 1 := by
    rw [← pow_four_eq' u, h4u]
  have hss : s * s = 1 := by rw [← h1]; exact huu2
  have huu_mem : u * u ∈ K ⊔ K' := by rw [h1]; exact hsmem
  have huu_z : u * u ≠ z := by rw [h1]; exact hsz
  have huN : u ∈ Subgroup.normalizer (K : Set G) := frameX_le_N d hu
  have huN' : u ∈ Subgroup.normalizer (K' : Set G) := (sec20X_le_normalizers_frame d hu).2
  obtain ⟨hKu, hK'u⟩ := not_innerOn_of_sq d hu huu_mem huu2 hu1 huu_z
  obtain ⟨e⟩ := kbar_equiv_q8 d
  obtain ⟨v₀, hv₀V, -, hv₀1, hv₀t⟩ := exists_gen_V d
  have hv₀X : v₀ ∈ X := le_sec20X_of_USet d d.hV (le_trans d.hVS d.hSz) hv₀V
  have hv₀N : v₀ ∈ Subgroup.normalizer (K : Set G) := frameX_le_N d hv₀X
  have hv₀N' : v₀ ∈ Subgroup.normalizer (K' : Set G) := (sec20X_le_normalizers_frame d hv₀X).2
  obtain ⟨hKv, hK'v⟩ := frame203Outer G K K' J S R R' W V z t d v₀ hv₀V hv₀1
  have ht2 : t * t = 1 := d.viol.hzJ.sq
  have ht1 : t ≠ 1 := d.viol.hzJ.ne_one
  have htz : t ≠ z := d.late_ne_inv
  have hz2 : z * z = 1 := d.viol.hzK.sq
  have hv₀4 : v₀ ^ 4 = 1 := by
    rw [pow_four_eq', hv₀t, ht2]
  have hpu4 : psiK K ⟨u, huN⟩ * psiK K ⟨u, huN⟩ = 1 := by
    apply pow_four_sq_eq_one (card_idx2_of_equiv_q8 e)
    have h4s : (⟨u, huN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 4 = 1 :=
      Subtype.ext (by simpa using h4u)
    rw [← map_pow, h4s, map_one]
  have hpu1 : psiK K ⟨u, huN⟩ ≠ 1 := fun h => hKu ((psiK_eq_one_iff K e _).mp h)
  have hpv4 : psiK K ⟨v₀, hv₀N⟩ * psiK K ⟨v₀, hv₀N⟩ = 1 := by
    apply pow_four_sq_eq_one (card_idx2_of_equiv_q8 e)
    have h4s : (⟨v₀, hv₀N⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 4 = 1 :=
      Subtype.ext (by simpa using hv₀4)
    rw [← map_pow, h4s, map_one]
  have hpv1 : psiK K ⟨v₀, hv₀N⟩ ≠ 1 := fun h => hKv ((psiK_eq_one_iff K e _).mp h)
  have hyX : v₀ * u ∈ X := X.mul_mem hv₀X hu
  have hyN : v₀ * u ∈ Subgroup.normalizer (K : Set G) := mul_mem hv₀N huN
  have hyN' : v₀ * u ∈ Subgroup.normalizer (K' : Set G) := mul_mem hv₀N' huN'
  have hu'X0 : (v₀ * u) * v₀ * (v₀ * u)⁻¹ ∈ X :=
    X.mul_mem (X.mul_mem hyX hv₀X) (X.inv_mem hyX)
  obtain ⟨u', hu'⟩ : ∃ u', u' = (v₀ * u) * v₀ * (v₀ * u)⁻¹ := ⟨_, rfl⟩
  have hu'X : u' ∈ X := by rw [hu']; exact hu'X0
  have hu'N : u' ∈ Subgroup.normalizer (K : Set G) := frameX_le_N d hu'X
  have hu'N' : u' ∈ Subgroup.normalizer (K' : Set G) := (sec20X_le_normalizers_frame d hu'X).2
  have hpsi : psiK K ⟨u', hu'N⟩ = psiK K ⟨u, huN⟩ := by
    have hw : (v₀ * u) * v₀ * (v₀ * u)⁻¹ ∈ Subgroup.normalizer (K : Set G) := by
      rw [← hu']; exact hu'N
    have hsub : (⟨u', hu'N⟩ : ↥(Subgroup.normalizer (K : Set G))) =
        ⟨(v₀ * u) * v₀ * (v₀ * u)⁻¹, hw⟩ := Subtype.ext hu'
    rw [hsub]
    exact psiK_dihedral d huN hv₀N hw hpu4 hpu1 hpv4 hpv1
  have hu'sq : u' * u' = (v₀ * u) * t * (v₀ * u)⁻¹ := by
    have e1 : u' * u' = (v₀ * u) * (v₀ * v₀) * (v₀ * u)⁻¹ := by rw [hu']; group
    rw [e1, hv₀t]
  have hu'2 : u' * u' * (u' * u') = 1 := by
    rw [hu'sq]
    calc (v₀ * u) * t * (v₀ * u)⁻¹ * ((v₀ * u) * t * (v₀ * u)⁻¹)
        = (v₀ * u) * (t * t) * (v₀ * u)⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  have hu'4 : u' ^ 4 = 1 := by rw [pow_four_eq', hu'2]
  have hu'mem : u' * u' ∈ K ⊔ K' := by
    rw [hu'sq]; exact conj_mem_sup_of_mem d hyN hyN' d.htKK
  have hu'z : u' * u' ≠ z := by
    intro h
    apply htz
    rw [hu'sq] at h
    calc t = (v₀ * u)⁻¹ * ((v₀ * u) * t * (v₀ * u)⁻¹) * (v₀ * u) := by group
      _ = (v₀ * u)⁻¹ * z * (v₀ * u) := by rw [h]
      _ = z := hconjz _ hyX
  have hu'1 : u' * u' ≠ 1 := by
    intro h
    apply ht1
    rw [hu'sq] at h
    calc t = (v₀ * u)⁻¹ * ((v₀ * u) * t * (v₀ * u)⁻¹) * (v₀ * u) := by group
      _ = 1 := by rw [h]; group
  have hKsq : (u * u)⁻¹ * (u' * u') ∈ trivialOnQuot K :=
    sq_inv_mul_mem_trivialOnQuot d huN hu'N hpsi.symm h4u hu'4
      (not_trivialOnQuot_of_invol d huu_mem huu2 hu1 huu_z)
      (not_trivialOnQuot_of_invol d hu'mem hu'2 hu'1 hu'z)
  obtain ⟨g, hg, hgK⟩ := d.swap
  have hgz : g * z = z * g := Subgroup.mem_centralizer_singleton_iff.mp hg
  have haN : g⁻¹ * u * g ∈ Subgroup.normalizer (K : Set G) :=
    conj_swap_mem_normalizer d hg hgK huN'
  have hbN : g⁻¹ * v₀ * g ∈ Subgroup.normalizer (K : Set G) :=
    conj_swap_mem_normalizer d hg hgK hv₀N'
  have hx'N : g⁻¹ * u' * g ∈ Subgroup.normalizer (K : Set G) :=
    conj_swap_mem_normalizer d hg hgK hu'N'
  set a := g⁻¹ * u * g with ha
  set b := g⁻¹ * v₀ * g with hb
  have hx'eq : g⁻¹ * u' * g = (b * a) * b * (b * a)⁻¹ := by
    rw [hu', ha, hb]; group
  have hbaN : (b * a) * b * (b * a)⁻¹ ∈ Subgroup.normalizer (K : Set G) := by
    rw [← hx'eq]; exact hx'N
  have ha4 : a ^ 4 = 1 := by rw [ha, conj_inv_pow, h4u]; group
  have hb4 : b ^ 4 = 1 := by rw [hb, conj_inv_pow, hv₀4]; group
  have hKa : ¬ InnerOn K a := fun h => hK'u (by rw [← hgK]; exact innerOn_swap h)
  have hKb : ¬ InnerOn K b := fun h => hK'v (by rw [← hgK]; exact innerOn_swap h)
  have hpa4 : psiK K ⟨a, haN⟩ * psiK K ⟨a, haN⟩ = 1 := by
    apply pow_four_sq_eq_one (card_idx2_of_equiv_q8 e)
    have h4s : (⟨a, haN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 4 = 1 :=
      Subtype.ext (by simpa using ha4)
    rw [← map_pow, h4s, map_one]
  have hpa1 : psiK K ⟨a, haN⟩ ≠ 1 := fun h => hKa ((psiK_eq_one_iff K e _).mp h)
  have hpb4 : psiK K ⟨b, hbN⟩ * psiK K ⟨b, hbN⟩ = 1 := by
    apply pow_four_sq_eq_one (card_idx2_of_equiv_q8 e)
    have h4s : (⟨b, hbN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 4 = 1 :=
      Subtype.ext (by simpa using hb4)
    rw [← map_pow, h4s, map_one]
  have hpb1 : psiK K ⟨b, hbN⟩ ≠ 1 := fun h => hKb ((psiK_eq_one_iff K e _).mp h)
  have hpsi' : psiK K ⟨(b * a) * b * (b * a)⁻¹, hbaN⟩ = psiK K ⟨a, haN⟩ :=
    psiK_dihedral d haN hbN hbaN hpa4 hpa1 hpb4 hpb1
  have hsub : (⟨g⁻¹ * u' * g, hx'N⟩ : ↥(Subgroup.normalizer (K : Set G))) =
      ⟨(b * a) * b * (b * a)⁻¹, hbaN⟩ := Subtype.ext hx'eq
  have hact' : psiK K ⟨a, haN⟩ = psiK K ⟨g⁻¹ * u' * g, hx'N⟩ := by
    rw [hsub, hpsi']
  have hsa_mem : a * a ∈ K ⊔ K' := by
    have e5 : a * a = g⁻¹ * (u * u) * g := by rw [ha]; group
    rw [e5]; exact conj_swap_sup d hg hgK huu_mem
  have hsa2 : a * a * (a * a) = 1 := by
    have e5 : a * a * (a * a) = g⁻¹ * (u * u * (u * u)) * g := by rw [ha]; group
    rw [e5, huu2]; group
  have hsa1 : a * a ≠ 1 := by
    intro h
    apply hu1
    have e5 : a * a = g⁻¹ * (u * u) * g := by rw [ha]; group
    have e6 : u * u = g * (a * a) * g⁻¹ := by rw [e5]; group
    rw [e6, h]; group
  have hsaz : a * a ≠ z := by
    intro h
    apply huu_z
    have e5 : a * a = g⁻¹ * (u * u) * g := by rw [ha]; group
    have e6 : u * u = g * (a * a) * g⁻¹ := by rw [e5]; group
    rw [e6, h, hgz]; group
  have hsx_mem : (g⁻¹ * u' * g) * (g⁻¹ * u' * g) ∈ K ⊔ K' := by
    have e6 : (g⁻¹ * u' * g) * (g⁻¹ * u' * g) = g⁻¹ * (u' * u') * g := by group
    rw [e6]; exact conj_swap_sup d hg hgK hu'mem
  have hsx2 : (g⁻¹ * u' * g) * (g⁻¹ * u' * g) * ((g⁻¹ * u' * g) * (g⁻¹ * u' * g)) = 1 := by
    have e6 : (g⁻¹ * u' * g) * (g⁻¹ * u' * g) * ((g⁻¹ * u' * g) * (g⁻¹ * u' * g)) =
        g⁻¹ * (u' * u' * (u' * u')) * g := by group
    rw [e6, hu'2]; group
  have hsx1 : (g⁻¹ * u' * g) * (g⁻¹ * u' * g) ≠ 1 := by
    intro h
    apply hu'1
    have e6 : (g⁻¹ * u' * g) * (g⁻¹ * u' * g) = g⁻¹ * (u' * u') * g := by group
    have e7 : u' * u' = g * ((g⁻¹ * u' * g) * (g⁻¹ * u' * g)) * g⁻¹ := by rw [e6]; group
    rw [e7, h]; group
  have hsxz : (g⁻¹ * u' * g) * (g⁻¹ * u' * g) ≠ z := by
    intro h
    apply hu'z
    have e6 : (g⁻¹ * u' * g) * (g⁻¹ * u' * g) = g⁻¹ * (u' * u') * g := by group
    have e7 : u' * u' = g * ((g⁻¹ * u' * g) * (g⁻¹ * u' * g)) * g⁻¹ := by rw [e6]; group
    rw [e7, h, hgz]; group
  have hx'4 : (g⁻¹ * u' * g) ^ 4 = 1 := by rw [conj_inv_pow, hu'4]; group
  have hK'sq : (a * a)⁻¹ * ((g⁻¹ * u' * g) * (g⁻¹ * u' * g)) ∈ trivialOnQuot K :=
    sq_inv_mul_mem_trivialOnQuot d haN hx'N hact' ha4 hx'4
      (not_trivialOnQuot_of_invol d hsa_mem hsa2 hsa1 hsaz)
      (not_trivialOnQuot_of_invol d hsx_mem hsx2 hsx1 hsxz)
  have e7 : (a * a)⁻¹ * ((g⁻¹ * u' * g) * (g⁻¹ * u' * g)) =
      g⁻¹ * ((u * u)⁻¹ * (u' * u')) * g := by
    rw [ha]; group
  rw [e7] at hK'sq
  have hwK' : (u * u)⁻¹ * (u' * u') ∈ trivialOnQuot K' := by
    have h := trivialOnQuot_conjSub hK'sq g
    rw [hgK, show g * (g⁻¹ * ((u * u)⁻¹ * (u' * u')) * g) * g⁻¹ = (u * u)⁻¹ * (u' * u') by group]
      at h
    exact h
  have hw_mem : (u * u)⁻¹ * (u' * u') ∈ K ⊔ K' :=
    (K ⊔ K').mul_mem ((K ⊔ K').inv_mem huu_mem) hu'mem
  obtain ⟨c, hc, n, hn, hwc⟩ := exists_central_mul_oddCore_sup d hw_mem hKsq hwK'
  have hnX : n ∈ X := hKK'X (oddCoreOf_le_self (K ⊔ K') hn)
  have hodd : Odd (orderOf n) :=
    Odd.of_dvd_nat (oddCoreOf_odd_natCard (K ⊔ K')) (Subgroup.orderOf_dvd_natCard _ hn)
  have hinv : (u * u)⁻¹ = s := by rw [← h1]; exact inv_eq_of_mul_eq_one_right huu2
  rw [hinv] at hwc
  rcases hc with hc1 | hc1
  ·
    rw [hc1, one_mul] at hwc
    exact exists_conj_of_one_case hss hu'2 hnX hodd hwc hyX hu'sq
  ·
    rw [hc1] at hwc
    have hcs : s * z = z * s := (z_comm_sup d hsmem).symm
    have hsz2 : (s * z) * (s * z) = 1 := by
      calc (s * z) * (s * z) = s * (z * s) * z := by group
        _ = s * (s * z) * z := by rw [← hcs]
        _ = (s * s) * (z * z) := by group
        _ = 1 := by rw [hss, hz2, mul_one]
    have hvE : u' * u' = s * (z * n) := eq_mul_of_invol_mul_eq hss hwc
    have hsv : (s * z) * (u' * u') = n := by
      rw [hvE]
      calc (s * z) * (s * (z * n)) = ((s * z) * (s * z)) * n := by group
        _ = n := by rw [hsz2, one_mul]
    obtain ⟨r, hr, -, -, -, hrt⟩ := d.late_tor d.late_JW d.late_hW
    have hrX : r ∈ X := hKK'X (Subgroup.mem_sup_left (d.hR.1 hr))
    have hP : z * (u' * u') = ((v₀ * u) * r) * t * ((v₀ * u) * r)⁻¹ := by
      rw [hu'sq]
      calc z * ((v₀ * u) * t * (v₀ * u)⁻¹) = ((z * (v₀ * u)) * t) * (v₀ * u)⁻¹ := by group
        _ = (((v₀ * u) * z) * t) * (v₀ * u)⁻¹ := by rw [hcomm _ hyX]
        _ = (v₀ * u) * (z * t) * (v₀ * u)⁻¹ := by group
        _ = (v₀ * u) * (r * t * r⁻¹) * (v₀ * u)⁻¹ := by rw [← hrt]
        _ = ((v₀ * u) * r) * t * ((v₀ * u) * r)⁻¹ := by group
    exact exists_conj_of_z_case hz2 hss hcs hu'2 hcomm (hcomm _ (X.mul_mem hu'X hu'X)).symm
      hnX hodd hsv
      (X.mul_mem hyX hrX) hP

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
