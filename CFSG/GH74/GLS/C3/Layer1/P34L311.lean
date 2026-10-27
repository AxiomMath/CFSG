module

public import CFSG.GH74.GLS.C3.Layer1.P34Basic

public section

namespace CFSG.GH74.GLS.C3.Layer1.P34

open Subgroup CFSG.GH74.GLS.Bg.Thompson CFSG.Quasithin

variable {X : Type} [Group X] [Finite X] {T P Q : Subgroup X} {x z f h : X}

theorem lemma310 (c : Cfg34 X T P Q x z f h) (hAlp : AlperinStep) (hOdd : OddMove)
    (core : ∀ {D : Subgroup X} {g : X}, D ≤ T → P ≤ D → g ∈ normalizer (D : Set X) →
      Odd (orderOf g) → (∃ a ∈ P, g⁻¹ * a * g ∉ P) → False) : Lemma310 T P := by
  intro g hgT
  by_contra hcon
  push Not at hcon
  obtain ⟨D, hPD, hDT, hidx, n, hn, a, ha, hna⟩ :=
    hAlp X T P c.T_pgroup c.T_index c.P_le ⟨g, hgT, hcon⟩
  set N : Subgroup X := normalizer (D : Set X) with hN
  let H : Subgroup N := (normalizer (P : Set X)).comap N.subtype
  have hTN : ((T ⊓ N).subgroupOf N) ≤ H := by
    intro m hm
    have hmT : (m : X) ∈ T := ((Subgroup.mem_subgroupOf.1 hm)).1
    show (m : X) ∈ normalizer (P : Set X)
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      exact c.P_norm _ hmT b hb
    · intro hb
      have := c.P_norm _ (T.inv_mem hmT) _ hb
      simpa [mul_assoc] using this
  have hHidx : ¬ 2 ∣ H.index := by
    intro h2
    apply hidx
    exact h2.trans (Subgroup.index_dvd_of_le hTN)
  have hHtop : H ≠ ⊤ := by
    intro htop
    have : (⟨n, hn⟩ : N) ∈ H := by rw [htop]; exact Subgroup.mem_top _
    have hnP : n ∈ normalizer (P : Set X) := this
    have hinv := (normalizer (P : Set X)).inv_mem hnP
    have := (Subgroup.mem_normalizer_iff.1 hinv) a
    apply hna
    have h3 := (this.1 ha)
    simpa using h3
  obtain ⟨m, hmodd, hmH⟩ := hOdd N H hHidx hHtop
  refine core hDT hPD m.2 (by rw [Subgroup.orderOf_coe m]; exact hmodd) ?_
  by_contra hno
  push Not at hno
  apply hmH
  exact mem_normalizer_of_conj_le hno

theorem lemma311 (c : Cfg34 X T P Q x z f h) (h310 : Lemma310 T P) : Lemma311 T P z := by
  intro u huT hucP hu2 hext
  obtain ⟨hUle, hUp, hUidx⟩ := hext
  set U : Subgroup X := T ⊓ centralizer ({u} : Set X) with hU
  have hCeq : T ⊓ centralizer ({u * z} : Set X) = U := by
    ext t
    constructor
    · rintro ⟨htT, ht⟩
      refine ⟨htT, mem_centralizer_singleton_iff.2 ?_⟩
      have h1 : t * (u * z) = (u * z) * t := mem_centralizer_singleton_iff.1 ht
      have h2 : z * t = t * z := (c.z_cent_T t htT).symm
      have : t * u * z = u * t * z := by
        calc t * u * z = t * (u * z) := by group
          _ = (u * z) * t := h1
          _ = u * (z * t) := by group
          _ = u * (t * z) := by rw [h2]
          _ = u * t * z := by group
      exact mul_right_cancel this
    · rintro ⟨htT, ht⟩
      refine ⟨htT, mem_centralizer_singleton_iff.2 ?_⟩
      have h1 : t * u = u * t := mem_centralizer_singleton_iff.1 ht
      have h2 : t * z = z * t := c.z_cent_T t htT
      calc t * (u * z) = (t * u) * z := by group
        _ = (u * t) * z := by rw [h1]
        _ = u * (t * z) := by group
        _ = u * (z * t) := by rw [h2]
        _ = (u * z) * t := by group
  obtain ⟨S, hUS, hSN, hSp, hSidx⟩ := exists_sylow_ge
    (N := centralizer ({u * z} : Set X)) (K := U) (by rw [← hCeq]; exact inf_le_right) hUp
  have hPU : P ≤ U := fun a ha =>
    ⟨c.P_le ha, mem_centralizer_singleton_iff.2 (hucP a ha).symm⟩
  obtain ⟨y, -, hy⟩ := exists_conj_into_sylow (p := 2) (N := ⊤) (K := S) (S₀ := T) le_top hSp
    le_top c.T_pgroup (by rw [Subgroup.relIndex_top_right]; exact c.T_index)
  have hPy : ∀ a ∈ P, y⁻¹ * a * y ∈ T := fun a ha => hy a (hUS (hPU ha))
  have hPy' : ∀ a ∈ P, y⁻¹ * a * y ∈ P := h310 y hPy
  have hynorm : y ∈ normalizer (P : Set X) := mem_normalizer_of_conj_le hPy'
  have hPS : ∀ s ∈ S, ∀ a ∈ P, s * a * s⁻¹ ∈ P := by
    intro s hs a ha
    have htT : y⁻¹ * s * y ∈ T := hy s hs
    have h1 : y⁻¹ * a * y ∈ P := hPy' a ha
    have h2 : (y⁻¹ * s * y) * (y⁻¹ * a * y) * (y⁻¹ * s * y)⁻¹ ∈ P := c.P_norm _ htT _ h1
    have h3 := ((Subgroup.mem_normalizer_iff.1 hynorm) _).1 h2
    have e : s * a * s⁻¹ = y * ((y⁻¹ * s * y) * (y⁻¹ * a * y) * (y⁻¹ * s * y)⁻¹) * y⁻¹ := by group
    rw [e]
    exact h3
  have hzS : ∀ s ∈ S, s * z = z * s := fun s hs =>
    c.z_cent_of_norm s (fun a ha => hPS s hs a ha) (fun a ha => by
      simpa using hPS s⁻¹ (S.inv_mem hs) a ha)
  have huzS : u * z ∈ S := by
    apply hUS
    refine ⟨T.mul_mem huT c.z_mem_T, mem_centralizer_singleton_iff.2 ?_⟩
    have h1 : u * z = z * u := c.z_cent_T u huT
    calc u * z * u = u * (z * u) := by group
      _ = u * (u * z) := by rw [← h1]
  have hSu : ∀ s ∈ S, s * u = u * s := by
    intro s hs
    have h1 : s * (u * z) = (u * z) * s := mem_centralizer_singleton_iff.1 (hSN hs)
    have h2 : s * z = z * s := hzS s hs
    calc s * u = s * (u * z) * z⁻¹ := by group
      _ = (u * z) * s * z⁻¹ := by rw [h1]
      _ = u * (z * s) * z⁻¹ := by group
      _ = u * (s * z) * z⁻¹ := by rw [← h2]
      _ = u * s := by group
  have hSC : S ≤ centralizer ({u} : Set X) := fun s hs =>
    mem_centralizer_singleton_iff.2 (hSu s hs)
  have hSU : S ≤ U := le_of_sylow_le hUS hSC hSp hUidx
  have hSeq : U = S := le_antisymm hUS hSU
  refine ⟨?_, ?_, ?_⟩
  · exact inf_le_right
  · rw [hCeq, hSeq]; exact hSp
  · rw [hCeq, hSeq]; exact hSidx

theorem lemma312 (c : Cfg34 X T P Q x z f h) (h35 : Lemma35 T P Q f) (h38 : Lemma38 T P z)
    (h310 : Lemma310 T P) (h311 : Lemma311 T P z) : Lemma312 T P Q z f := by
  obtain ⟨g, hfR, hCT, hext⟩ := h35
  have hPgT : ∀ a ∈ P, g⁻¹ * a * g ∈ T := fun a ha => hCT a (c.P_le ha) (c.f_cent a ha).symm
  have hPgP : ∀ a ∈ P, g⁻¹ * a * g ∈ P := h310 g hPgT
  have hgN : g ∈ normalizer (P : Set X) := mem_normalizer_of_conj_le hPgP
  have hzg : g⁻¹ * z * g = z := h38 g hPgT
  have hf₁C : ∀ a ∈ P, (g⁻¹ * f * g) * a = a * (g⁻¹ * f * g) := by
    intro a ha
    have hb : g * a * g⁻¹ ∈ P := ((Subgroup.mem_normalizer_iff.1 hgN) a).1 ha
    have := c.f_cent _ hb
    calc (g⁻¹ * f * g) * a = g⁻¹ * (f * (g * a * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * a * g⁻¹) * f) * g := by rw [this]
      _ = a * (g⁻¹ * f * g) := by group
  obtain ⟨p, hp, q, hq, hpq⟩ := c.mem_PQ.1 hfR
  have hpZ : ∀ a ∈ P, a * p = p * a := by
    intro a ha
    have h1 := hf₁C a ha
    have hqa := c.PQ_comm a ha q hq
    have : p * a * q = a * p * q := by
      calc p * a * q = p * (a * q) := by group
        _ = p * (q * a) := by rw [hqa]
        _ = (p * q) * a := by group
        _ = (g⁻¹ * f * g) * a := by rw [← hpq]
        _ = a * (g⁻¹ * f * g) := h1
        _ = a * p * q := by rw [hpq]; group
    exact (mul_right_cancel this).symm
  have hf₁2 : (g⁻¹ * f * g) * (g⁻¹ * f * g) = 1 := by
    calc (g⁻¹ * f * g) * (g⁻¹ * f * g) = g⁻¹ * (f * f) * g := by group
      _ = 1 := by rw [c.f_sq]; group
  have hf₁T : g⁻¹ * f * g ∈ T := c.R_le hfR
  have hzCT : ∀ t ∈ T, t * (f * z) = (f * z) * t → t * f = f * t := by
    intro t htT ht
    have h2 : t * z = z * t := c.z_cent_T t htT
    have : t * f * z = f * t * z := by
      calc t * f * z = t * (f * z) := by group
        _ = (f * z) * t := ht
        _ = f * (z * t) := by group
        _ = f * (t * z) := by rw [← h2]
        _ = f * t * z := by group
    exact mul_right_cancel this
  rcases c.z_unique p hp (fun a ha => hpZ a ha) with h1 | h1
  ·
    refine ⟨f, g, Or.inl rfl, hgN, ?_, hext, hCT⟩
    have : g⁻¹ * f * g = q := by rw [hpq, h1, one_mul]
    rw [this]; exact hq
  ·
    have hqz : g⁻¹ * (f * z) * g = q := by
      have e : g⁻¹ * (f * z) * g = (g⁻¹ * f * g) * (g⁻¹ * z * g) := by group
      rw [e, hzg, hpq, h1]
      have hzq : z * q = q * z := c.PQ_comm z c.z_mem q hq
      calc z * q * z = q * z * z := by rw [hzq]
        _ = q * (z * z) := by group
        _ = q := by rw [c.z_sq, mul_one]
    refine ⟨f * z, g, Or.inr rfl, hgN, ?_, ?_, ?_⟩
    · rw [hqz]; exact hq
    · have h311' := h311 (g⁻¹ * f * g) hf₁T (fun a ha => hf₁C a ha) hf₁2 hext
      have e : g⁻¹ * (f * z) * g = (g⁻¹ * f * g) * z := by
        have e1 : g⁻¹ * (f * z) * g = (g⁻¹ * f * g) * (g⁻¹ * z * g) := by group
        rw [e1, hzg]
      rw [e]; exact h311'
    · intro t htT ht
      exact hCT t htT (hzCT t htT ht)

end CFSG.GH74.GLS.C3.Layer1.P34
