module

public import CFSG.GH74.Generic.BProg.B3.S3Sec29D1

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG Subgroup
open scoped commutatorElement

namespace S3Sec29D3

variable {X : Type*} [Group X]

@[expose] def CommConj (J : Subgroup X) (g : X) : Prop :=
  ∀ a ∈ J, ∀ b ∈ J, a * (g * b * g⁻¹) = (g * b * g⁻¹) * a

@[expose] def diagHom (J : Subgroup X) (g : X) (hc : CommConj J g) : ↥J →* X where
  toFun c := (c : X) * (g * c * g⁻¹)
  map_one' := by simp
  map_mul' c d := by
    have h1 := hc d d.2 c c.2
    simp only [Subgroup.coe_mul]
    calc (c : X) * d * (g * (c * d) * g⁻¹)
        = c * (d * (g * c * g⁻¹)) * (g * d * g⁻¹) := by group
      _ = c * ((g * c * g⁻¹) * d) * (g * d * g⁻¹) := by rw [h1]
      _ = c * (g * c * g⁻¹) * (d * (g * d * g⁻¹)) := by group

theorem diagHom_apply {J : Subgroup X} {g : X} (hc : CommConj J g) (c : ↥J) :
    diagHom J g hc c = (c : X) * (g * c * g⁻¹) := rfl

theorem diagHom_comm {J : Subgroup X} {g : X} (hc : CommConj J g) (hg : g * g = 1) (c : ↥J) :
    diagHom J g hc c * g = g * diagHom J g hc c := by
  have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  have h1 := hc c c.2 c c.2
  rw [diagHom_apply]
  rw [hgi] at h1 ⊢
  calc (c : X) * (g * c * g) * g = (c * (g * c * g)) * g := rfl
    _ = ((g * c * g) * c) * g := by rw [h1]
    _ = g * (c * (g * c * g)) := by
        calc (g * c * g) * c * g = g * c * (g * c * g) := by group
          _ = g * (c * (g * c * g)) := by group

theorem diag_perfect {J : Subgroup X} {g : X} (hc : CommConj J g) (hp : Group.IsPerfect ↥J) :
    ⁅(diagHom J g hc).range, (diagHom J g hc).range⁆ = (diagHom J g hc).range := by
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator]
  congr 1
  exact hp.commutator_eq_top

theorem central_of_diag_eq_one {J : Subgroup X} {g : X} (hc : CommConj J g) {c : ↥J}
    (h1 : diagHom J g hc c = 1) : ∀ d : ↥J, c * d = d * c := by
  intro d
  rw [diagHom_apply] at h1
  have hci : (c : X) = (g * c * g⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left h1
  have h2 := hc d d.2 c c.2
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  rw [hci]
  have h3 : (g * c * g⁻¹)⁻¹ * d = d * (g * c * g⁻¹)⁻¹ := by
    calc (g * c * g⁻¹)⁻¹ * (d : X) = (g * c * g⁻¹)⁻¹ * (d * (g * c * g⁻¹)) * (g * c * g⁻¹)⁻¹ := by
          group
      _ = (g * c * g⁻¹)⁻¹ * ((g * c * g⁻¹) * d) * (g * c * g⁻¹)⁻¹ := by rw [h2]
      _ = d * (g * c * g⁻¹)⁻¹ := by group
  exact h3

theorem diag_odd_normal {J : Subgroup X} {g : X} (hc : CommConj J g) (hq : IsQuasisimple ↥J)
    {z : ↥J} (hz : SL2Data ↥J z) {N : Subgroup X} (hNr : N ≤ (diagHom J g hc).range)
    (hNn : ∀ d ∈ (diagHom J g hc).range, ∀ n ∈ N, d * n * d⁻¹ ∈ N) (hodd : Odd (Nat.card ↥N)) :
    N = ⊥ := by
  set φ := diagHom J g hc with hφ
  have hN4 : (N.comap φ).Normal := ⟨fun n hn c => by
    show φ (c * n * c⁻¹) ∈ N
    rw [map_mul, map_mul, map_inv]
    exact hNn (φ c) ⟨c, rfl⟩ (φ n) hn⟩
  have hodd_ord : ∀ n ∈ N, n * n = 1 → n = 1 := by
    intro n hn hnn
    have h1 : orderOf n ∣ Nat.card ↥N := Subgroup.orderOf_dvd_natCard N hn
    have h2 : orderOf n ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hnn)
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
    · exact orderOf_eq_one_iff.1 h
    · rw [h] at h1
      exact absurd (Nat.odd_iff.1 hodd) (by have := Nat.mod_eq_zero_of_dvd h1; omega)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hN4 with htop | hcen
  · exfalso
    obtain ⟨t, ht⟩ := hz.exists_sq
    have htN : φ t ∈ N := by
      have : t ∈ N.comap φ := by rw [htop]; trivial
      exact this
    have hne : φ t ≠ 1 := by
      intro h1
      have hcen := central_of_diag_eq_one hc h1
      rcases hz.center_eq t hcen with h | h
      · rw [h, one_mul] at ht; exact hz.z_ne ht.symm
      · rw [h] at ht; exact hz.z_ne (ht.symm.trans hz.z_sq)
    have h4 : (φ t) ^ 4 = 1 := by
      rw [← map_pow]
      have : t ^ 4 = 1 := by
        calc t ^ 4 = (t * t) * (t * t) := by simp [pow_succ, mul_assoc]
          _ = 1 := by rw [ht, hz.z_sq]
      rw [this, map_one]
    have h1 : orderOf (φ t) ∣ Nat.card ↥N := Subgroup.orderOf_dvd_natCard N htN
    have h2 : orderOf (φ t) ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one (by simpa using h4)
    obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
    rcases Nat.eq_zero_or_pos i with hi0 | hi0
    · rw [hi0, pow_zero] at hio
      exact hne (orderOf_eq_one_iff.1 hio)
    · have h2d : 2 ∣ orderOf (φ t) := by
        rw [hio]; exact dvd_pow_self 2 (by omega)
      have := Nat.mod_eq_zero_of_dvd (h2d.trans h1)
      have := Nat.odd_iff.1 hodd
      omega
  · rw [eq_bot_iff]
    intro n hn
    obtain ⟨c, rfl⟩ := hNr hn
    have hc' : c ∈ center ↥J := hcen hn
    rcases hz.center_eq c (fun d => (Subgroup.mem_center_iff.1 hc' d).symm) with h | h
    · rw [h, map_one]; exact one_mem _
    · rw [h] at hn ⊢
      have : φ z * φ z = 1 := by rw [← map_mul, hz.z_sq, map_one]
      rw [hodd_ord (φ z) hn this]
      exact one_mem _

theorem le_diag_sup {J : Subgroup X} {g h : X} (hcg : CommConj J g) (hcgh : CommConj J (g * h))
    (hq : IsQuasisimple ↥J) (hh : h ∈ normalizer (J : Set X)) (hhne : ∃ c ∈ J, h * c * h⁻¹ ≠ c) :
    J ≤ (diagHom J g hcg).range ⊔ (diagHom J (g * h) hcgh).range := by
  have : Group.IsPerfect ↥J := hq.1
  set 𝒟 := (diagHom J g hcg).range ⊔ (diagHom J (g * h) hcgh).range with h𝒟
  have key : ∀ c : ↥J, g * ((c : X)⁻¹ * (h * c * h⁻¹)) * g⁻¹ ∈ 𝒟 := by
    intro c
    have e : g * ((c : X)⁻¹ * (h * c * h⁻¹)) * g⁻¹ =
        (diagHom J g hcg c)⁻¹ * diagHom J (g * h) hcgh c := by
      rw [diagHom_apply, diagHom_apply]; group
    rw [e]
    exact mul_mem (inv_mem (Subgroup.mem_sup_left ⟨c, rfl⟩)) (Subgroup.mem_sup_right ⟨c, rfl⟩)
  let σ : ↥J →* ↥J :=
    { toFun := fun c => ⟨h * c * h⁻¹, (Subgroup.mem_normalizer_iff.1 hh c).1 c.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by apply Subtype.ext; simp only [Subgroup.coe_mul]; group }
  have hσ : ∀ c : ↥J, ((σ c : ↥J) : X) = h * c * h⁻¹ := fun c => rfl
  set S : Set ↥J := Set.range (fun c : ↥J => c⁻¹ * σ c) with hS
  have hconj : ∀ d : ↥J, ∀ s ∈ S, d * s * d⁻¹ ∈ Subgroup.closure S := by
    rintro d _ ⟨c, rfl⟩
    have e : d * (c⁻¹ * σ c) * d⁻¹ =
        ((c * d⁻¹)⁻¹ * σ (c * d⁻¹)) * (d⁻¹⁻¹ * σ d⁻¹)⁻¹ := by
      rw [map_mul, map_inv]; group
    rw [e]
    exact mul_mem (Subgroup.subset_closure ⟨c * d⁻¹, rfl⟩)
      (inv_mem (Subgroup.subset_closure ⟨d⁻¹, rfl⟩))
  have hNn : (Subgroup.closure S).Normal := ⟨fun n hn d => by
    induction hn using Subgroup.closure_induction with
    | mem s hs => exact hconj d s hs
    | one => simp
    | mul a b _ _ ha hb =>
        have := mul_mem ha hb
        rwa [show d * (a * b) * d⁻¹ = (d * a * d⁻¹) * (d * b * d⁻¹) by group]
    | inv a _ ha =>
        have := inv_mem ha
        rwa [show d * a⁻¹ * d⁻¹ = (d * a * d⁻¹)⁻¹ by group]⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hNn with htop | hcen
  · have hgJ : ∀ c : ↥J, g * (c : X) * g⁻¹ ∈ 𝒟 := by
      intro c
      have hc : c ∈ Subgroup.closure S := by rw [htop]; trivial
      induction hc using Subgroup.closure_induction with
      | mem s hs =>
          obtain ⟨c', rfl⟩ := hs
          have := key c'
          simpa [hσ] using this
      | one => simp
      | mul a b _ _ ha hb =>
          have := mul_mem ha hb
          rwa [show g * ((a * b : ↥J) : X) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) by
            simp only [Subgroup.coe_mul]; group]
      | inv a _ ha =>
          have := inv_mem ha
          rwa [show g * ((a⁻¹ : ↥J) : X) * g⁻¹ = (g * a * g⁻¹)⁻¹ by
            simp only [Subgroup.coe_inv]; group]
    intro c hc
    have e : c = diagHom J g hcg ⟨c, hc⟩ * (g * c * g⁻¹)⁻¹ := by
      rw [diagHom_apply]; group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left ⟨⟨c, hc⟩, rfl⟩) (inv_mem (hgJ ⟨c, hc⟩))
  · exfalso
    have hdisp : ∀ c : ↥J, c⁻¹ * σ c ∈ Subgroup.center ↥J :=
      fun c => hcen (Subgroup.subset_closure ⟨c, rfl⟩)
    have hid := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement σ hdisp
    obtain ⟨c, hcJ, hne⟩ := hhne
    apply hne
    have := congrArg (fun f : ↥J →* ↥J => ((f ⟨c, hcJ⟩ : ↥J) : X)) hid
    simpa [hσ] using this

theorem exists_D8 {J : Subgroup X} {g : X} (hcg : CommConj J g) {z : ↥J} (hz : SL2Data ↥J z)
    (hzc : ∀ v : X, v * (z : X) = (z : X) * v) {u t : X} (htJ : t ∈ J) (hu2 : u * u = 1)
    (huJ : ∀ c ∈ J, u * c * u⁻¹ = t * c * t⁻¹) (hut : ∃ c ∈ J, u * c * u⁻¹ ≠ c)
    (hug : u * g = g * u) :
    ∃ a w : X, a ∈ J ⊔ J.map (MulAut.conj g).toMonoidHom ∧
      w ∈ J ⊔ J.map (MulAut.conj g).toMonoidHom ∧
      a * u = u * a ∧ w * u = u * w ∧ a * a = z ∧ w * w = 1 ∧ w * a * w⁻¹ = a⁻¹ := by
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have htt : ∀ c ∈ J, (t * t) * c = c * (t * t) := by
    intro c hc
    have h1 : u * (u * c * u⁻¹) * u⁻¹ = c := by
      calc u * (u * c * u⁻¹) * u⁻¹ = (u * u) * c * (u⁻¹ * u⁻¹) := by group
        _ = c := by rw [hu2, hui, hu2]; group
    have htc : t * c * t⁻¹ ∈ J := J.mul_mem (J.mul_mem htJ hc) (J.inv_mem htJ)
    rw [huJ c hc, huJ _ htc] at h1
    calc (t * t) * c = (t * (t * c * t⁻¹) * t⁻¹) * (t * t) := by group
      _ = c * (t * t) := by rw [h1]
  set tJ : ↥J := ⟨t, htJ⟩ with htJdef
  have htt' : tJ * tJ = 1 ∨ tJ * tJ = z := by
    refine hz.center_eq (tJ * tJ) (fun d => Subtype.ext ?_)
    simpa using htt d d.2
  have hzt : tJ * tJ = z := by
    rcases htt' with h1 | h1
    · exfalso
      obtain ⟨c, hc, hne⟩ := hut
      rcases hz.invol_eq tJ h1 with h2 | h2
      · have : t = 1 := congrArg Subtype.val h2
        apply hne; rw [huJ c hc, this]; group
      · have : t = (z : X) := congrArg Subtype.val h2
        apply hne; rw [huJ c hc, this, ← hzc c]; group
    · exact h1
  have hzz : (z : X) * z = 1 := congrArg Subtype.val hz.z_sq
  have hzi : (z : X)⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have htz : t * t = z := congrArg Subtype.val hzt
  obtain ⟨sJ, hss, hst⟩ := hz.invert tJ hzt
  set s : X := (sJ : X) with hsdef
  have hsJ : s ∈ J := sJ.2
  have hss' : s * s = z := congrArg Subtype.val hss
  have hst' : s * t * s⁻¹ = t⁻¹ := congrArg Subtype.val hst
  have hts : t * s * t⁻¹ = s * z := by
    have h1 : s * t⁻¹ * s⁻¹ = t := by
      have := congrArg (fun v : X => v⁻¹) hst'
      simpa [mul_assoc] using this
    calc t * s * t⁻¹ = (s * t⁻¹ * s⁻¹) * s * t⁻¹ := by rw [h1]
      _ = s * (t * t)⁻¹ := by group
      _ = s * z := by rw [htz, hzi]
  have hcs : ∀ c ∈ J, c * (g * s * g⁻¹) = (g * s * g⁻¹) * c := fun c hc => hcg c hc s hsJ
  refine ⟨t, s * (g * s * g⁻¹), Subgroup.mem_sup_left htJ,
    mul_mem (Subgroup.mem_sup_left hsJ) (Subgroup.mem_sup_right ⟨s, hsJ, rfl⟩), ?_, ?_, htz, ?_, ?_⟩
  · have := huJ t htJ
    calc t * u = u * (u⁻¹ * t * u) := by group
      _ = u * (u * t * u⁻¹) := by rw [hui]
      _ = u * t := by rw [this]; group
  · have hus : u * s * u⁻¹ = s * z := by rw [huJ s hsJ, hts]
    have hugs : u * (g * s * g⁻¹) * u⁻¹ = (g * s * g⁻¹) * z := by
      calc u * (g * s * g⁻¹) * u⁻¹ = (u * g) * s * (u * g)⁻¹ := by group
        _ = (g * u) * s * (g * u)⁻¹ := by rw [hug]
        _ = g * (u * s * u⁻¹) * g⁻¹ := by group
        _ = g * (s * z) * g⁻¹ := by rw [hus]
        _ = (g * s * g⁻¹) * (g * z * g⁻¹) := by group
        _ = (g * s * g⁻¹) * (z * g * g⁻¹) := by rw [hzc g]
        _ = (g * s * g⁻¹) * z := by group
    have hw : u * (s * (g * s * g⁻¹)) * u⁻¹ = s * (g * s * g⁻¹) := by
      calc u * (s * (g * s * g⁻¹)) * u⁻¹ = (u * s * u⁻¹) * (u * (g * s * g⁻¹) * u⁻¹) := by group
        _ = (s * z) * ((g * s * g⁻¹) * z) := by rw [hus, hugs]
        _ = s * (z * (g * s * g⁻¹)) * z := by group
        _ = s * ((g * s * g⁻¹) * z) * z := by rw [← hzc (g * s * g⁻¹)]
        _ = s * (g * s * g⁻¹) * (z * z) := by group
        _ = s * (g * s * g⁻¹) := by rw [hzz, mul_one]
    calc s * (g * s * g⁻¹) * u = u * (u⁻¹ * (s * (g * s * g⁻¹)) * u) := by group
      _ = u * (u * (s * (g * s * g⁻¹)) * u⁻¹) := by rw [hui]
      _ = u * (s * (g * s * g⁻¹)) := by rw [hw]
  · calc s * (g * s * g⁻¹) * (s * (g * s * g⁻¹)) = s * ((g * s * g⁻¹) * s) * (g * s * g⁻¹) := by group
      _ = s * (s * (g * s * g⁻¹)) * (g * s * g⁻¹) := by rw [← hcs s hsJ]
      _ = (s * s) * (g * (s * s) * g⁻¹) := by group
      _ = z * (g * z * g⁻¹) := by rw [hss']
      _ = z * (z * g * g⁻¹) := by rw [hzc g]
      _ = z * z := by group
      _ = 1 := hzz
  · calc s * (g * s * g⁻¹) * t * (s * (g * s * g⁻¹))⁻¹
        = s * ((g * s * g⁻¹) * t) * (g * s * g⁻¹)⁻¹ * s⁻¹ := by group
      _ = s * (t * (g * s * g⁻¹)) * (g * s * g⁻¹)⁻¹ * s⁻¹ := by rw [← hcs t htJ]
      _ = s * t * s⁻¹ := by group
      _ = t⁻¹ := hst'

end S3Sec29D3

end CFSG.GH74.Generic.BProg.B3
