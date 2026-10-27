module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L106A

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private lemma oTwoRes_le (X : Subgroup G) : oTwoRes X ≤ X := by
  unfold oTwoRes
  exact (Subgroup.closure_le X).2 (fun x hx => hx.1)

private lemma conj_good {t z h y : G} (hz2 : z * z = 1) (hh : h⁻¹ * t * h = t * z)
    (hhz : h⁻¹ * z * h = z) (hyt : y * t = t * y) (hyz : y * z = z * y) :
    (h * y * h⁻¹) * t = t * (h * y * h⁻¹) ∧
      (h * y * h⁻¹) * z = z * (h * y * h⁻¹) := by
  have hhz' : h * z * h⁻¹ = z := by
    have h1 : h * (h⁻¹ * z * h) * h⁻¹ = h * z * h⁻¹ := by rw [hhz]
    calc h * z * h⁻¹ = h * (h⁻¹ * z * h) * h⁻¹ := h1.symm
      _ = z := by group
  have hhtz : h * (t * z) * h⁻¹ = t := by
    have h1 : h * (h⁻¹ * t * h) * h⁻¹ = h * (t * z) * h⁻¹ := by rw [hh]
    calc h * (t * z) * h⁻¹ = h * (h⁻¹ * t * h) * h⁻¹ := h1.symm
      _ = t := by group
  have hzz : (t * z) * z = t := by rw [mul_assoc, hz2, mul_one]
  have hht : h * t * h⁻¹ = t * z := by
    calc h * t * h⁻¹ = h * ((t * z) * z) * h⁻¹ := by rw [hzz]
      _ = (h * (t * z) * h⁻¹) * (h * z * h⁻¹) := by group
      _ = t * z := by rw [hhtz, hhz']
  have hyz' : (h * y * h⁻¹) * z = z * (h * y * h⁻¹) := by
    calc (h * y * h⁻¹) * z = h * y * (h⁻¹ * z * h) * h⁻¹ := by group
      _ = h * y * z * h⁻¹ := by rw [hhz]
      _ = h * (y * z) * h⁻¹ := by group
      _ = h * (z * y) * h⁻¹ := by rw [hyz]
      _ = h * z * y * h⁻¹ := by group
      _ = (h * z * h⁻¹) * (h * y * h⁻¹) := by group
      _ = z * (h * y * h⁻¹) := by rw [hhz']
  have hkey : (h * y * h⁻¹) * (t * z) = (t * z) * (h * y * h⁻¹) := by
    rw [← hht]
    calc (h * y * h⁻¹) * (h * t * h⁻¹) = h * (y * t) * h⁻¹ := by group
      _ = h * (t * y) * h⁻¹ := by rw [hyt]
      _ = (h * t * h⁻¹) * (h * y * h⁻¹) := by group
  have hyt' : (h * y * h⁻¹) * t = t * (h * y * h⁻¹) := by
    calc (h * y * h⁻¹) * t = (h * y * h⁻¹) * ((t * z) * z) := by rw [hzz]
      _ = (h * y * h⁻¹) * (t * z) * z := by group
      _ = (t * z) * (h * y * h⁻¹) * z := by rw [hkey]
      _ = (t * z) * z * (h * y * h⁻¹) := by rw [mul_assoc, hyz', ← mul_assoc]
      _ = t * (h * y * h⁻¹) := by rw [hzz]
  exact ⟨hyt', hyz'⟩

theorem sec10K0_conj_mem {t z g : G} (hz2 : z * z = 1) (hg : g⁻¹ * t * g = t * z)
    (hgz : g⁻¹ * z * g = z) {x : G} (hx : x ∈ secK0 t z) :
    g⁻¹ * x * g ∈ secK0 t z ∧ g * x * g⁻¹ ∈ secK0 t z := by
  have hgz' : g * z * g⁻¹ = z := by
    have h1 : g * (g⁻¹ * z * g) * g⁻¹ = g * z * g⁻¹ := by rw [hgz]
    calc g * z * g⁻¹ = g * (g⁻¹ * z * g) * g⁻¹ := h1.symm
      _ = z := by group
  have hgtz : g * (t * z) * g⁻¹ = t := by
    have h1 : g * (g⁻¹ * t * g) * g⁻¹ = g * (t * z) * g⁻¹ := by rw [hg]
    calc g * (t * z) * g⁻¹ = g * (g⁻¹ * t * g) * g⁻¹ := h1.symm
      _ = t := by group
  have hzz : (t * z) * z = t := by rw [mul_assoc, hz2, mul_one]
  have hgt : g * t * g⁻¹ = t * z := by
    calc g * t * g⁻¹ = g * ((t * z) * z) * g⁻¹ := by rw [hzz]
      _ = (g * (t * z) * g⁻¹) * (g * z * g⁻¹) := by group
      _ = t * z := by rw [hgtz, hgz']
  have hall : ∀ h : G, h⁻¹ * t * h = t * z → h⁻¹ * z * h = z →
      (secK0 t z).map (MulAut.conj h).toMonoidHom ≤ secK0 t z := by
    intro h hh hhz
    rw [Subgroup.map_le_iff_le_comap]
    unfold secK0 oTwoRes
    refine (Subgroup.closure_le _).2 ?_
    intro w hw
    change (MulAut.conj h) w ∈ Subgroup.closure
      {x : G | x ∈ centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G) ∧ Odd (orderOf x)}
    obtain ⟨⟨hwt, hwz⟩, hwodd⟩ := hw
    have hgood := conj_good hz2 hh hhz
      (Subgroup.mem_centralizer_singleton_iff.mp hwt)
      (Subgroup.mem_centralizer_singleton_iff.mp hwz)
    refine Subgroup.subset_closure ⟨⟨?_, ?_⟩, ?_⟩
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hgood.1
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hgood.2
    · have hord : orderOf ((MulAut.conj h) w) = orderOf w :=
        MulEquiv.orderOf_eq (MulAut.conj h) w
      rw [hord]
      exact hwodd
  have hmem_g : g * x * g⁻¹ ∈ secK0 t z := by
    have hmap : (MulAut.conj g) x ∈ (secK0 t z).map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using hall g hg hgz hmap
  have hmem_ginv : g⁻¹ * x * g ∈ secK0 t z := by
    have hg' : (g⁻¹)⁻¹ * t * (g⁻¹) = t * z := by simpa using hgt
    have hgz'' : (g⁻¹)⁻¹ * z * (g⁻¹) = z := by simpa using hgz'
    have hmap : (MulAut.conj g⁻¹) x ∈ (secK0 t z).map (MulAut.conj g⁻¹).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using hall g⁻¹ hg' hgz'' hmap
  exact ⟨hmem_ginv, hmem_g⟩

theorem sec10K0_conj_oddCore [Finite G] (hK0 : Asc82Lemma10K0) (hP5 : Asc82FactPockets5)
    (hC5 : Asc82FactCentZ5) {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G}
    (hpsp : IsPSp43 L) (hctx : Sec10Ctx G t L S z K1 K2) {g : G} (hg : g⁻¹ * t * g = t * z)
    (hgz : g⁻¹ * z * g = z) {o : G} (ho : o ∈ oddCoreIn (centralizer ({t} : Set G))) :
    g * o * g⁻¹ ∈ oddCoreIn (centralizer ({t} : Set G)) := by
  let O : Subgroup G := oddCoreIn (centralizer ({t} : Set G))
  let K0 : Subgroup G := secK0 t z
  let K : Subgroup G := K1 ⊔ K2
  let N0 : Subgroup G := oddCoreIn K0
  let O' : Subgroup G := O.map (MulAut.conj g).toMonoidHom
  have hz2 : orderOf z = 2 := hctx.toSec10Z.pocket.1
  have hzsq : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  have hK0sec : secK0 t z = O ⊔ K1 ⊔ K2 := (hK0 G t L S z K1 K2 hctx).1
  have hK0leCt : K0 ≤ centralizer ({t} : Set G) := by
    change secK0 t z ≤ centralizer ({t} : Set G)
    unfold secK0
    exact le_trans (oTwoRes_le _) inf_le_left
  have hnormO : K0 ≤ Subgroup.normalizer (O : Set G) :=
    le_trans hK0leCt
      (CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn (centralizer ({t} : Set G)))
  have hoddO : Odd (Nat.card O) :=
    CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn (centralizer ({t} : Set G))
  have hOleK0 : O ≤ K0 := by
    change O ≤ secK0 t z
    rw [hK0sec]
    exact le_trans le_sup_left le_sup_left
  have hKleK0 : K ≤ K0 := by
    change K1 ⊔ K2 ≤ secK0 t z
    rw [hK0sec]
    exact sup_le (le_trans le_sup_right le_sup_left) le_sup_right
  have hOleN0 : O ≤ N0 :=
    CFSG.ClassicalInvolution.Balance.le_oddCoreIn_of_normalizes hOleK0 hnormO hoddO
  have hN0leK0 : N0 ≤ K0 := CFSG.ClassicalInvolution.Balance.oddCoreIn_le K0
  have hK0normN0 : K0 ≤ Subgroup.normalizer (N0 : Set G) :=
    CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn K0
  have hO'leK0 : O' ≤ K0 := by
    intro y hy
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hy
    have := (sec10K0_conj_mem hzsq hg hgz (hOleK0 hw)).2
    simpa [MulAut.conj_apply] using this
  have hK0normO' : K0 ≤ Subgroup.normalizer (O' : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro k hk y hy
    obtain ⟨w, hw, hyw⟩ := Subgroup.mem_map.mp hy
    rw [← hyw]
    refine Subgroup.mem_map.mpr ⟨(g⁻¹ * k * g) * w * (g⁻¹ * k * g)⁻¹, ?_, ?_⟩
    · have hkK0 : g⁻¹ * k * g ∈ K0 := (sec10K0_conj_mem hzsq hg hgz hk).1
      have hkC : g⁻¹ * k * g ∈ centralizer ({t} : Set G) := hK0leCt hkK0
      exact (Subgroup.mem_normalizer_iff.mp
        (CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn (centralizer ({t} : Set G))
          hkC) w).mp hw
    · show g * ((g⁻¹ * k * g) * w * (g⁻¹ * k * g)⁻¹) * g⁻¹ = k * (g * w * g⁻¹) * k⁻¹
      group
  have hO'odd : Odd (Nat.card O') := by
    have hcard : Nat.card O' = Nat.card O := by
      change Nat.card (O.map (MulAut.conj g).toMonoidHom) = Nat.card O
      exact Subgroup.card_map_of_injective (K := O) (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).injective
    rw [hcard]
    exact hoddO
  have hO'leN0 : O' ≤ N0 :=
    CFSG.ClassicalInvolution.Balance.le_oddCoreIn_of_normalizes hO'leK0 hK0normO' hO'odd
  have hN0K : N0 ⊓ K = ⊥ := by
    have hoddN0 : Odd (Nat.card N0) :=
      CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn K0
    have hodd : Odd (Nat.card (N0 ⊓ K : Subgroup G)) :=
      hoddN0.of_dvd_nat (Subgroup.card_dvd_of_le (inf_le_left : N0 ⊓ K ≤ N0))
    have hnorm : K ≤ Subgroup.normalizer ((N0 ⊓ K : Subgroup G) : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      intro k hk x hx
      rw [Subgroup.mem_inf] at hx ⊢
      refine ⟨?_, K.mul_mem (K.mul_mem hk hx.2) (K.inv_mem hk)⟩
      exact (Subgroup.mem_normalizer_iff.mp (hK0normN0 (hKleK0 hk)) x).mp hx.1
    have hle : N0 ⊓ K ≤ CFSG.ClassicalInvolution.Balance.oddCoreIn K :=
      CFSG.ClassicalInvolution.Balance.le_oddCoreIn_of_normalizes inf_le_right hnorm hodd
    have hbot : CFSG.ClassicalInvolution.Balance.oddCoreIn K = ⊥ := by
      change oddCoreIn (K1 ⊔ K2) = ⊥
      exact sec10_oddCoreIn_sup_pockets hP5 hC5 hpsp hctx
    rw [hbot] at hle
    exact le_bot_iff.mp hle
  have hK0KO : K0 = K ⊔ O := by
    change secK0 t z = K ⊔ O
    rw [hK0sec]
    change O ⊔ K1 ⊔ K2 = (K1 ⊔ K2) ⊔ O
    ac_rfl
  set y : G := g * o * g⁻¹ with hy
  have hyO' : y ∈ O' := Subgroup.mem_map.mpr ⟨o, ho, rfl⟩
  have hyN0 : y ∈ N0 := hO'leN0 hyO'
  have hyK0 : y ∈ K0 := hN0leK0 hyN0
  have hyKO : y ∈ K ⊔ O := hK0KO ▸ hyK0
  have hKO : K ≤ Subgroup.normalizer (O : Set G) := le_trans hKleK0 hnormO
  have hy' : y ∈ (↑(K ⊔ O) : Set G) := hyKO
  rw [Subgroup.coe_mul_of_left_le_normalizer_right K O hKO] at hy'
  obtain ⟨k, hk, o1, ho1, hko⟩ := Set.mem_mul.mp hy'
  have hk_eq : k = y * o1⁻¹ := by rw [← hko]; group
  have ho1N0 : o1⁻¹ ∈ N0 := N0.inv_mem (hOleN0 ho1)
  have hkN0 : k ∈ N0 := by
    rw [hk_eq]
    exact N0.mul_mem hyN0 ho1N0
  have hk1 : k = 1 := by
    have hbot : k ∈ (⊥ : Subgroup G) := by
      rw [← hN0K]
      exact ⟨hkN0, hk⟩
    simpa using hbot
  have hyo1 : y = o1 := by rw [← hko, hk1, one_mul]
  exact hyo1.symm ▸ ho1

end CFSG.OddStandard.SmallF3.Omega
