module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CB6
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10E1Cat
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10SidePgl
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CB3

public section

namespace CFSG.ComponentClassification.GSThmB.A10E1

open CFSG Subgroup Equiv Equiv.Perm CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.GSThmB.Seven CFSG.ComponentClassification.GSThmB.Eight2
open CFSG.ComponentClassification.GSThmB.A10Side

variable {X : Type} [Group X] [Finite X] (s : Setting3 X)

theorem index_Ct
    (hA : Nonempty (↥(generalizedFitting (s.h.subQuot s.y)) ≃* alternatingGroup (Fin 10))) :
    (s.Ct.subgroupOf s.Dt).index = 2 := by
  have h1 := s.two_mul_card_Ct hA
  have h2 : Nat.card s.Dt = Nat.card s.h.D := Seven.card_conjugate _ _
  have h3 := relIndex_mul_card (H := s.Ct) (K := s.Dt)
  rw [inf_eq_left.mpr inf_le_left] at h3
  have h4 : 0 < Nat.card s.Ct := Nat.card_pos
  change s.Ct.relIndex s.Dt = 2
  nlinarith

theorem exists_mem_Dt_not_mem_P
    (hA : Nonempty (↥(generalizedFitting (s.h.subQuot s.y)) ≃* alternatingGroup (Fin 10))) :
    ∃ d ∈ s.Dt, d ∉ s.h.P := by
  by_contra hcon
  push Not at hcon
  have hle : s.Dt ≤ s.Ct := fun d hd => mem_inf.mpr ⟨hd, hcon d hd⟩
  have h1 := s.two_mul_card_Ct hA
  have h2 : Nat.card s.Dt = Nat.card s.h.D := Seven.card_conjugate _ _
  have h3 : Nat.card s.Dt ≤ Nat.card s.Ct := card_le_of_le hle
  have h4 : 0 < Nat.card s.h.D := Nat.card_pos
  omega

theorem mul_self_mem_P
    (hA : Nonempty (↥(generalizedFitting (s.h.subQuot s.y)) ≃* alternatingGroup (Fin 10)))
    {d : X} (hd : d ∈ s.Dt) : d * d ∈ s.h.P := by
  have h := sq_mem_of_index_two (index_Ct s hA) ⟨d, hd⟩
  rw [mem_subgroupOf, Subgroup.coe_pow, pow_two] at h
  exact (mem_inf.mp h).2

theorem mul_inv_mem_P
    (hA : Nonempty (↥(generalizedFitting (s.h.subQuot s.y)) ≃* alternatingGroup (Fin 10)))
    {u d : X} (hu : u ∈ s.Dt) (hd : d ∈ s.Dt) (huP : u ∉ s.h.P) (hdP : d ∉ s.h.P) :
    u * d⁻¹ ∈ s.h.P := by
  have hmem : ∀ w : s.Dt, w ∈ s.Ct.subgroupOf s.Dt ↔ (w : X) ∈ s.h.P := fun w =>
    ⟨fun h => (mem_inf.mp (mem_subgroupOf.mp h)).2, fun h => mem_subgroupOf.mpr
      (mem_inf.mpr ⟨w.2, h⟩)⟩
  have h := (mul_mem_iff_of_index_two (index_Ct s hA) (a := ⟨u, hu⟩) (b := ⟨d, hd⟩⁻¹)).mpr
    (by rw [hmem, hmem]; exact ⟨fun h => absurd h huP, fun h => absurd
      (by simpa using (s.h.P.inv_mem h)) hdP⟩)
  exact (hmem _).mp h

theorem mem_normalizer_of_mem_S {g : X} (hg : g ∈ s.h.S) : g ∈ normalizer (s.h.J : Set X) :=
  (mem_inf.mp (s.h.S_le hg)).2

theorem conj_injective_Jbar : Function.Injective
    (MulAut.conj : (↥s.h.J ⧸ pPrimeCore 2 ↥s.h.J) →* MulAut (↥s.h.J ⧸ pPrimeCore 2 ↥s.h.J)) := by
  intro a b hab
  have hmem : b⁻¹ * a ∈ center (↥s.h.J ⧸ pPrimeCore 2 ↥s.h.J) := by
    rw [mem_center_iff]
    intro g
    have h1 := congrArg (fun φ : MulAut (↥s.h.J ⧸ pPrimeCore 2 ↥s.h.J) => φ g) hab
    simp only [MulAut.conj_apply] at h1
    calc g * (b⁻¹ * a) = b⁻¹ * (b * g * b⁻¹) * a := by group
      _ = b⁻¹ * (a * g * a⁻¹) * a := by rw [h1]
      _ = b⁻¹ * a * g := by group
  rw [s.center_J, mem_bot] at hmem
  calc a = b * (b⁻¹ * a) := by group
    _ = b := by rw [hmem, mul_one]

theorem exists_rhoE_of_mem_Dbar {t : ↥s.h.J ⧸ pPrimeCore 2 ↥s.h.J} (ht : t ∈ Dbar s.h) :
    ∃ w ∈ s.h.D, rhoE s.h.J w = MulAut.conj t := by
  obtain ⟨w, hw, rfl⟩ := mem_map.mp ht
  refine ⟨w, mem_subgroupOf.mp hw, ?_⟩
  rw [rhoE_of_mem_J w.2]
  rfl

theorem rhoE_comm {g k : X} (hg : g ∈ normalizer (s.h.J : Set X))
    (hk : k ∈ normalizer (s.h.J : Set X)) (h : g * k = k * g) :
    rhoE s.h.J g * rhoE s.h.J k = rhoE s.h.J k * rhoE s.h.J g := by
  rw [← rhoE_mul hg hk, ← rhoE_mul hk hg, h]

theorem mem_P_of_rhoE_eq_one {g : X} (hg : g ∈ s.h.S) (h1 : rhoE s.h.J g = 1) : g ∈ s.h.P :=
  mem_inf.mpr ⟨hg, (rhoE_eq_one_iff (mem_normalizer_of_mem_S s hg)).mp h1⟩

theorem rhoE_eq_one_of_mem_P {g : X} (hg : g ∈ s.h.P) : rhoE s.h.J g = 1 :=
  (rhoE_eq_one_iff (mem_normalizer_of_mem_S s (mem_inf.mp hg).1)).mpr (mem_inf.mp hg).2

omit [Finite X] in
theorem comm_of_mul_comm {a b c : X} (hcb : c * b = b * c)
    (h : (a * c) * b = b * (a * c)) : a * b = b * a := by
  apply mul_right_cancel (b := c)
  calc a * b * c = a * (c * b) := by rw [mul_assoc, hcb]
    _ = a * c * b := (mul_assoc _ _ _).symm
    _ = b * (a * c) := h
    _ = b * a * c := (mul_assoc _ _ _).symm

theorem sign_eq_neg_one (Z : ZData s.h) (hJo : CFSec8JOrder)
    (hA : Nonempty (↥(generalizedFitting (s.h.subQuot s.y)) ≃* alternatingGroup (Fin 10)))
    (e : ↥s.h.J ⧸ pPrimeCore 2 ↥s.h.J ≃* alternatingGroup (Fin 6)) {d : X} (hd : d ∈ s.Dt)
    (hdP : d ∉ s.h.P) {σ : Perm (Fin 6)}
    (hσ : MulAut.congr e (rhoE s.h.J d) = MulAut.conjNormal σ) : sign σ = -1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hs : sign σ = 1 := (Int.units_eq_one_or (sign σ)).resolve_right hne
  have hdS := s.Dt_le_S hd
  have hdN := mem_normalizer_of_mem_S s hdS
  set σA : alternatingGroup (Fin 6) := ⟨σ, mem_alternatingGroup.mpr hs⟩ with hσA
  set jb := e.symm σA with hjb
  have hρd : rhoE s.h.J d = MulAut.conj jb := by
    apply (MulAut.congr e).injective
    rw [hσ, congr_conj, hjb, MulEquiv.apply_symm_apply, ← MulAut.conjNormal_val]
  have hjbC : ∀ t ∈ Dbar s.h, t * jb = jb * t := by
    intro t ht
    obtain ⟨w, hwD, hwρ⟩ := exists_rhoE_of_mem_Dbar s ht
    have hwN := mem_normalizer_of_mem_S s (s.h.D_le_S hwD)
    have h1 := rhoE_comm s hwN hdN (s.D_comm_Dt hwD hd)
    rw [hwρ, hρd, ← map_mul, ← map_mul] at h1
    exact conj_injective_Jbar s h1
  have hjb2 : jb * jb = 1 := by
    have h1 := rhoE_eq_one_of_mem_P s (mul_self_mem_P s hA hd)
    rw [rhoE_mul hdN hdN, hρd, ← map_mul] at h1
    exact conj_injective_Jbar s (h1.trans (map_one _).symm)
  have hjbD : jb ∈ Dbar s.h := by
    obtain ⟨T, hT⟩ := Z.sylow
    have hp2 : IsPGroup 2 (zpowers jb) := by
      have hdvd : orderOf jb ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, hjb2])
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
      · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
    have hle : zpowers jb ≤ normalizer (Dbar s.h : Set _) := by
      rw [zpowers_le]
      refine mem_normalizer_iff.mpr fun t => ⟨fun ht => ?_, fun ht => ?_⟩
      · have h1 : jb * t * jb⁻¹ = t := by rw [← hjbC t ht, mul_inv_cancel_right]
        rw [h1]
        exact ht
      · have h1 := hjbC _ ht
        have h2 : t = jb * t * jb⁻¹ := by
          calc t = jb⁻¹ * ((jb * t * jb⁻¹) * jb) := by group
            _ = jb⁻¹ * (jb * (jb * t * jb⁻¹)) := by rw [h1]
            _ = jb * t * jb⁻¹ := by group
        rw [h2]
        exact ht
    have hDp : IsPGroup 2 (Dbar s.h) := hT ▸ T.isPGroup'
    have hsup := hp2.to_sup_of_normal_right' hDp hle
    have hT' : (T : Subgroup _) ≤ zpowers jb ⊔ Dbar s.h := hT ▸ le_sup_right
    have heq := T.is_maximal' (hT ▸ hsup) hT'
    rw [← hT, ← heq]
    exact mem_sup_left (mem_zpowers jb)
  have hρdz : rhoE s.h.J d = rhoE s.h.J Z.z := by
    rcases Z.hZD jb hjbD (mem_centralizer_iff.mpr hjbC) with h | h
    · exact absurd (mem_P_of_rhoE_eq_one s hdS (hρd.trans h)) hdP
    · exact hρd.trans h
  have hzS := s.h.D_le_S Z.hzD
  have hzN := mem_normalizer_of_mem_S s hzS
  have hcor : ∀ u ∈ s.Dt, ∃ c : X, (c = 1 ∨ c = Z.z) ∧ u * c ∈ s.h.P := by
    intro u hu
    by_cases huP : u ∈ s.h.P
    · exact ⟨1, Or.inl rfl, by rwa [mul_one]⟩
    · refine ⟨Z.z, Or.inr rfl, mem_P_of_rhoE_eq_one s (mul_mem (s.Dt_le_S hu) hzS) ?_⟩
      have huN := mem_normalizer_of_mem_S s (s.Dt_le_S hu)
      have h1 := rhoE_eq_one_of_mem_P s (mul_inv_mem_P s hA hu hd huP hdP)
      rw [rhoE_mul huN (inv_mem hdN), rhoE_inv hdN, mul_inv_eq_one, hρdz] at h1
      rw [rhoE_mul huN hzN, h1, ← rhoE_mul hzN hzN, Z.hzz, rhoE_one]
  obtain ⟨u, hu, v, hv, huv⟩ : ∃ u ∈ s.Dt, ∃ v ∈ s.Dt, u * v ≠ v * u := by
    by_contra hcon
    push Not at hcon
    have hDle : s.h.D ≤ zpowers Z.z := by
      intro w hw
      have hcen : ∀ w' ∈ s.h.D, w * w' = w' * w := by
        intro w' hw'
        have h1 := hcon (s.t⁻¹ * w * s.t) (by rw [mem_conjugate_iff]; group; exact hw)
          (s.t⁻¹ * w' * s.t) (by rw [mem_conjugate_iff]; group; exact hw')
        have h2 : s.t⁻¹ * (w * w') * s.t = s.t⁻¹ * (w' * w) * s.t := by
          calc s.t⁻¹ * (w * w') * s.t = s.t⁻¹ * w * s.t * (s.t⁻¹ * w' * s.t) := by group
            _ = s.t⁻¹ * w' * s.t * (s.t⁻¹ * w * s.t) := h1
            _ = s.t⁻¹ * (w' * w) * s.t := by group
        exact mul_left_cancel (mul_right_cancel h2)
      rcases Z.hZDz w hw hcen with h | h
      · rw [h]
        exact one_mem _
      · rw [h]
        exact mem_zpowers _
    have h8 := Eight2.card_D_ge_eight hJo s.case8
    have h2 : Nat.card (zpowers Z.z) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (by rw [pow_two, Z.hzz]) Z.hz1
    have h3 := card_le_of_le hDle
    omega
  obtain ⟨c, hc, hucP⟩ := hcor u hu
  obtain ⟨c', hc', hvcP⟩ := hcor v hv
  have hcS : ∀ c₀ : X, c₀ = 1 ∨ c₀ = Z.z → ∀ g ∈ s.h.S, c₀ * g = g * c₀ := by
    rintro c₀ (rfl | rfl) g hg
    · rw [one_mul, mul_one]
    · exact (Z.hzS g hg).symm
  have hcD : ∀ c₀ : X, c₀ = 1 ∨ c₀ = Z.z → c₀ ∈ s.h.D := by
    rintro c₀ (rfl | rfl)
    · exact one_mem _
    · exact Z.hzD
  have hne : (u * c) * (v * c') ≠ (v * c') * (u * c) := by
    intro h
    apply huv
    have h1 : v * (u * c) = (u * c) * v := by
      refine comm_of_mul_comm (a := v) (b := u * c) (c := c')
        (hcS c' hc' _ (mul_mem (s.Dt_le_S hu) (s.h.D_le_S (hcD c hc)))) ?_
      exact h.symm
    exact comm_of_mul_comm (hcS c hc v (s.Dt_le_S hv)) h1.symm
  have hG0 : ∀ g ∈ s.h.D ⊔ s.Dt, g ∈ s.h.secG0 s.y := fun g hg => s.D_sup_Dt_le_G0 hg
  have hH : ∀ g ∈ s.h.D ⊔ s.Dt, g ∈ s.h.secSub s.y := fun g hg => s.D_sup_Dt_le_secSub hg
  have hu' : u * c ∈ s.h.D ⊔ s.Dt := mul_mem (mem_sup_right hu) (mem_sup_left (hcD c hc))
  have hv' : v * c' ∈ s.h.D ⊔ s.Dt := mul_mem (mem_sup_right hv) (mem_sup_left (hcD c' hc'))
  have hF : ∀ g (hg : g ∈ s.h.D ⊔ s.Dt), s.h.subQ s.y ⟨g, hH g hg⟩ ∈
      generalizedFitting (s.h.subQuot s.y) := by
    intro g hg
    have hsup : s.sec.S ⊓ s.sec.J ⊔ conjugate (s.sec.S ⊓ s.sec.J) s.tb ≤
        generalizedFitting (s.h.subQuot s.y) := s.D_sup ▸ inf_le_right
    have hmap : ((s.h.D ⊔ s.Dt).subgroupOf (s.h.secSub s.y)).map (s.h.subQ s.y) ≤
        generalizedFitting (s.h.subQuot s.y) := by
      rw [Subgroup.subgroupOf_sup s.D_le_secSub s.Dt_le_secSub, Subgroup.map_sup, s.map_D_eq,
        s.map_Dt_eq]
      exact hsup
    exact hmap (mem_map_of_mem _ (mem_subgroupOf.mpr hg))
  have hPH : ∀ g (hg : g ∈ s.h.D ⊔ s.Dt), g ∈ s.h.P → s.h.subQ s.y ⟨g, hH g hg⟩ ∈
      s.sec.toHyp52.P := fun g hg hgP => s.subQ_mem_secP hgP (hG0 g hg) (hH g hg)
  have hmemH : ∀ g (hg : g ∈ s.h.D ⊔ s.Dt), g ∈ s.h.P → s.h.subQ s.y ⟨g, hH g hg⟩ ∈
      generalizedFitting (s.h.subQuot s.y) ⊓ centralizer ({s.sec.a} : Set _) ⊓
        coreActionKernel s.sec.J := by
    intro g hg hgP
    have h1 := hPH g hg hgP
    exact mem_inf.mpr ⟨mem_inf.mpr ⟨hF g hg, (mem_inf.mp (s.sec.S_le (mem_inf.mp h1).1)).1⟩,
      (mem_inf.mp h1).2⟩
  have hcomm := commute_of_mem_inf s.hp s.hp2 s.hf s.centralizer_eq hA s.sec.orderOf_a
    s.sec.J_le s.sec.isPComponent_J s.J_type (hmemH _ hu' hucP) (hmemH _ hv' hvcP)
  apply hne
  set w := (u * c) * (v * c') * (u * c)⁻¹ * (v * c')⁻¹ with hw
  have hwD : w ∈ s.h.D ⊔ s.Dt :=
    mul_mem (mul_mem (mul_mem hu' hv') (inv_mem hu')) (inv_mem hv')
  have hw1 : s.h.subQ s.y ⟨w, hH w hwD⟩ = 1 := by
    have h1 : (⟨w, hH w hwD⟩ : ↥(s.h.secSub s.y)) = ⟨u * c, hH _ hu'⟩ * ⟨v * c', hH _ hv'⟩ *
        ⟨u * c, hH _ hu'⟩⁻¹ * ⟨v * c', hH _ hv'⟩⁻¹ := Subtype.ext rfl
    rw [h1, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  obtain ⟨k, hk⟩ := s.h.isPGroup_S ⟨w, s.D_sup_Dt_le_S hwD⟩
  have hk' : (w : X) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hwB := secQ_eq_one_of_two (w := ⟨w, hH w hwD⟩) hk' hw1
  have hw0 : w = 1 := by
    have h1 := s.D_sup_Dt_inf_B0 ▸ mem_inf.mpr ⟨hwD, hwB⟩
    exact (mem_bot.mp h1)
  calc (u * c) * (v * c') = w * ((v * c') * (u * c)) := by rw [hw]; group
    _ = (v * c') * (u * c) := by rw [hw0, one_mul]

theorem mul_self_eq_one
    (hA : Nonempty (↥(generalizedFitting (s.h.subQuot s.y)) ≃* alternatingGroup (Fin 10)))
    (e : ↥s.h.J ⧸ pPrimeCore 2 ↥s.h.J ≃* alternatingGroup (Fin 6)) {d : X} (hd : d ∈ s.Dt)
    {σ : Perm (Fin 6)} (hσ : MulAut.congr e (rhoE s.h.J d) = MulAut.conjNormal σ) :
    σ * σ = 1 := by
  have hdN := mem_normalizer_of_mem_S s (s.Dt_le_S hd)
  have h1 := rhoE_eq_one_of_mem_P s (mul_self_mem_P s hA hd)
  rw [rhoE_mul hdN hdN] at h1
  have h2 := congrArg (MulAut.congr e) h1
  rw [map_mul, hσ, map_one, ← map_mul] at h2
  exact CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 6 (by norm_num)
    (h2.trans (map_one _).symm)

theorem exists_q (Z : ZData s.h) (e : ↥s.h.J ⧸ pPrimeCore 2 ↥s.h.J ≃* alternatingGroup (Fin 6))
    {d : X} (hd : d ∈ s.Dt) {σ : Perm (Fin 6)}
    (hσ : MulAut.congr e (rhoE s.h.J d) = MulAut.conjNormal σ) :
    ∃ q : Perm (Fin 6), sign q = 1 ∧ q ^ 4 = 1 ∧ q ^ 2 ≠ 1 ∧ σ * q = q * σ ∧
      MulAut.conjNormal (q ^ 2) = MulAut.congr e (rhoE s.h.J Z.z) := by
  obtain ⟨t, htD, htt, htC⟩ := Z.hsq
  have hdN := mem_normalizer_of_mem_S s (s.Dt_le_S hd)
  have hzN := mem_normalizer_of_mem_S s (s.h.D_le_S Z.hzD)
  have hconj : ∀ j : ↥s.h.J ⧸ pPrimeCore 2 ↥s.h.J,
      MulAut.conjNormal ((e j : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
        MulAut.congr e (MulAut.conj j) := fun j => by
    rw [congr_conj, MulAut.conjNormal_val]
  have htt' : MulAut.conj (t * t) = rhoE s.h.J Z.z := by
    rcases Z.hZD (t * t) (mul_mem htD htD) htC with h | h
    · exact absurd (conj_injective_Jbar s (h.trans (map_one _).symm)) htt
    · exact h
  refine ⟨(e t : Perm (Fin 6)), mem_alternatingGroup.mp (e t).2, ?_, ?_, ?_, ?_⟩
  · have h1 : MulAut.conj (t * t * (t * t)) = 1 := by
      rw [map_mul, htt', ← rhoE_mul hzN hzN, Z.hzz, rhoE_one]
    have h2 := conj_injective_Jbar s (h1.trans (map_one _).symm)
    have h3 : (e t : Perm (Fin 6)) ^ 4 = ((e (t * t * (t * t)) : alternatingGroup (Fin 6)) :
        Perm (Fin 6)) := by
      rw [map_mul, map_mul, show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, sq, sq]
      simp only [Subgroup.coe_mul]
    rw [h3, h2, map_one]
    rfl
  · intro h
    apply htt
    apply e.injective
    rw [map_mul, map_one]
    apply Subtype.ext
    rw [Subgroup.coe_mul, ← pow_two]
    exact h
  · obtain ⟨w, hwD, hwρ⟩ := exists_rhoE_of_mem_Dbar s htD
    have hwN := mem_normalizer_of_mem_S s (s.h.D_le_S hwD)
    have h1 := congrArg (MulAut.congr e) (rhoE_comm s hdN hwN (s.D_comm_Dt hwD hd).symm)
    rw [map_mul, map_mul, hσ, hwρ, ← hconj, ← map_mul, ← map_mul] at h1
    exact CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 6 (by norm_num) h1
  · have h1 : (e t : Perm (Fin 6)) ^ 2 = ((e (t * t) : alternatingGroup (Fin 6)) :
        Perm (Fin 6)) := by
      rw [map_mul, Subgroup.coe_mul, pow_two]
    rw [h1, hconj, htt']

end CFSG.ComponentClassification.GSThmB.A10E1
