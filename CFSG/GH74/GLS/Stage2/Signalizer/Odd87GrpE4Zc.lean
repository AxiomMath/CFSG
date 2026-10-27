module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpE4Sl2Basic
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpU
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpSwap

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section
variable {A : Type} [Group A]

theorem zc_identity {J : Subgroup A} {y₁ y₂ j c' : A} (hy₁ : y₁ ∈ J)
    (hy₂ : y₂ ∈ centralizer (J : Set A)) (hj : j ∈ J) (hc : c' ∈ centralizer (J : Set A)) :
    y₁ * (j * c') * y₁⁻¹ =
      ((y₁ * y₂) * (j * c') * (y₁ * y₂)⁻¹) * ((y₂ * c' * y₂⁻¹)⁻¹ * c') := by
  have e1 : y₂ * j = j * y₂ := by
    have := Subgroup.mem_centralizer_iff.mp hy₂ j hj
    exact this.symm
  have e2 : c' * y₁ = y₁ * c' := (Subgroup.mem_centralizer_iff.mp hc y₁ hy₁).symm
  have hd : y₂ * c' * y₂⁻¹ ∈ centralizer (J : Set A) :=
    mul_mem (mul_mem hy₂ hc) (inv_mem hy₂)
  have e3 : (y₂ * c' * y₂⁻¹) * y₁ = y₁ * (y₂ * c' * y₂⁻¹) :=
    (Subgroup.mem_centralizer_iff.mp hd y₁ hy₁).symm
  have e1' : y₂ * j * y₂⁻¹ = j := by rw [e1]; group
  have e2' : y₁ * c' * y₁⁻¹ = c' := by rw [← e2]; group
  have e3' : y₁ * (y₂ * c' * y₂⁻¹) * y₁⁻¹ = y₂ * c' * y₂⁻¹ := by rw [← e3]; group
  calc y₁ * (j * c') * y₁⁻¹ = (y₁ * j * y₁⁻¹) * (y₁ * c' * y₁⁻¹) := by group
    _ = (y₁ * j * y₁⁻¹) * c' := by rw [e2']
    _ = (y₁ * j * y₁⁻¹) * (y₁ * (y₂ * c' * y₂⁻¹) * y₁⁻¹) * ((y₂ * c' * y₂⁻¹)⁻¹ * c') := by
        rw [e3']; group
    _ = (y₁ * (y₂ * j * y₂⁻¹) * y₁⁻¹) * (y₁ * (y₂ * c' * y₂⁻¹) * y₁⁻¹) * ((y₂ * c' * y₂⁻¹)⁻¹ * c') := by
        rw [e1']
    _ = ((y₁ * y₂) * (j * c') * (y₁ * y₂)⁻¹) * ((y₂ * c' * y₂⁻¹)⁻¹ * c') := by group
end

section
variable {G : Type} [Group G] {z : G}
variable {A : Type} [Group A] [Finite A] {a : A} {p : ℕ} {X : Subgroup A}

theorem secJ_central_two {c : E4Ctx G z A a p X} {J : Subgroup A} (d : SubData c J)
    {ω : secB a X J} (hω : ω ∈ secJ a X J) (hc : ∀ b ∈ secJ a X J, ω * b = b * ω) :
    ∃ r : ℕ, ω ^ (2 ^ r) = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH := secB_Hyp42 d.hyp
  have hL := secB_layer d.hyp
  have hωL : ω ∈ layer (secB a X J) := hL ▸ hω
  have hcen : (⟨ω, hωL⟩ : ↥(layer (secB a X J))) ∈ center ↥(layer (secB a X J)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact (hc g.1 (hL ▸ g.2)).symm
  rw [hH.2.2.1] at hcen
  have hpg : IsPGroup 2 ↥(pCore 2 ↥(layer (secB a X J))) := pCore_isPGroup
  obtain ⟨r, hr⟩ := hpg ⟨_, hcen⟩
  refine ⟨r, ?_⟩
  have := congrArg (fun t : ↥(pCore 2 ↥(layer (secB a X J))) => ((t : ↥(layer (secB a X J))) : secB a X J)) hr
  simpa using this


theorem zc_conj_mem {c : E4Ctx G z A a p X} {J : Subgroup A} (d : SubData c J)
    (h : Sl2Cl p (secZ a X J) (secX a X J) (secJ a X J))
    {y₁ y₂ : A} (hy₁ : y₁ ∈ J) (hy₂ : y₂ ∈ centralizer (J : Set A))
    (hu : y₁ * y₂ ∈ normalizer (X : Set A)) {x : A} (hx : x ∈ X) :
    secMk a X J y₁ (J_le_secY a X J hy₁) * secMk a X J x (X_le_secY a X J hx) *
      (secMk a X J y₁ (J_le_secY a X J hy₁))⁻¹ ∈ secX a X J := by
  have hcomm : ∀ j ∈ J, ∀ c' ∈ centralizer (J : Set A), j * c' = c' * j := fun j hj c' hc' =>
    Subgroup.mem_centralizer_iff.mp hc' j hj
  obtain ⟨j, hj, c', hc', hxjc⟩ := exists_mul_of_mem_sup hcomm (d.X_le_sup h hx)
  have hx' : (y₁ * y₂) * x * (y₁ * y₂)⁻¹ ∈ X := (mem_normalizer_iff.mp hu x).mp hx
  set x' := (y₁ * y₂) * x * (y₁ * y₂)⁻¹ with hx'def
  have hw : (y₂ * c' * y₂⁻¹)⁻¹ * c' ∈ centralizer (J : Set A) :=
    mul_mem (inv_mem (mul_mem (mul_mem hy₂ hc') (inv_mem hy₂))) hc'
  set w := (y₂ * c' * y₂⁻¹)⁻¹ * c' with hwdef
  have hid : y₁ * x * y₁⁻¹ = x' * w := by
    have := zc_identity hy₁ hy₂ hj hc'
    rw [hxjc] at this
    exact this
  have h1 : y₁ ∈ secY a X J := J_le_secY a X J hy₁
  have hxY : x ∈ secY a X J := X_le_secY a X J hx
  have hx'Y : x' ∈ secY a X J := X_le_secY a X J hx'
  have hconjY : y₁ * x * y₁⁻¹ ∈ secY a X J := mul_mem (mul_mem h1 hxY) (inv_mem h1)
  have hwY : w ∈ secY a X J := by
    have : w = x'⁻¹ * (y₁ * x * y₁⁻¹) := by rw [hid]; group
    rw [this]
    exact mul_mem (inv_mem hx'Y) hconjY
  have hB : secMk a X J y₁ h1 * secMk a X J x hxY * (secMk a X J y₁ h1)⁻¹ =
      secMk a X J x' hx'Y * secMk a X J w hwY := by
    rw [← secMk_inv h1, ← secMk_mul h1 hxY, ← secMk_mul (mul_mem h1 hxY) (inv_mem h1),
      ← secMk_mul hx'Y hwY]
    exact secMk_congr hid _ _
  have hb₁ : secMk a X J y₁ h1 ∈ secJ a X J := secMk_mem_secJ hy₁
  have hbx : secMk a X J x hxY ∈ secJ a X J := h.X_le (secMk_mem_secX hx)
  have hbx' : secMk a X J x' hx'Y ∈ secJ a X J := h.X_le (secMk_mem_secX hx')
  have hg : secMk a X J y₁ h1 * secMk a X J x hxY * (secMk a X J y₁ h1)⁻¹ ∈ secJ a X J :=
    mul_mem (mul_mem hb₁ hbx) (inv_mem hb₁)
  have hbw : secMk a X J w hwY ∈ secJ a X J := by
    have : secMk a X J w hwY =
        (secMk a X J x' hx'Y)⁻¹ * (secMk a X J y₁ h1 * secMk a X J x hxY * (secMk a X J y₁ h1)⁻¹) := by
      rw [hB]; group
    rw [this]
    exact mul_mem (inv_mem hbx') hg
  have hcentral : ∀ b ∈ secJ a X J, secMk a X J w hwY * b = b * secMk a X J w hwY := by
    intro b hb
    obtain ⟨j', hj', rfl⟩ := mem_secJ_iff.mp hb
    rw [← secMk_mul hwY (J_le_secY a X J hj'), ← secMk_mul (J_le_secY a X J hj') hwY]
    exact secMk_congr (Subgroup.mem_centralizer_iff.mp hw j' hj').symm _ _
  obtain ⟨r, hr⟩ := secJ_central_two d hbw hcentral
  have hpg := c.A4.pgroup
  obtain ⟨m₁, hm₁⟩ := hpg ⟨x, hx⟩
  obtain ⟨m₂, hm₂⟩ := hpg ⟨x', hx'⟩
  have hcop : Nat.Coprime (p ^ (m₁ + m₂)) (2 ^ r) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes c.A4.prime Nat.prime_two).mpr c.A4.odd)
  have hxN : x ^ (p ^ (m₁ + m₂)) = 1 := by
    have h' : x ^ (p ^ m₁) = 1 := by simpa using congrArg Subtype.val hm₁
    rw [pow_add, pow_mul, h', one_pow]
  have hx'N : x' ^ (p ^ (m₁ + m₂)) = 1 := by
    have h' : x' ^ (p ^ m₂) = 1 := by simpa using congrArg Subtype.val hm₂
    rw [add_comm, pow_add, pow_mul, h', one_pow]
  have hbxN : secMk a X J x hxY ^ (p ^ (m₁ + m₂)) = 1 := by
    rw [← secMk_pow hxY]; rw [secMk_congr hxN _ (secY a X J).one_mem, secMk_one]
  have hbx'N : secMk a X J x' hx'Y ^ (p ^ (m₁ + m₂)) = 1 := by
    rw [← secMk_pow hx'Y]; rw [secMk_congr hx'N _ (secY a X J).one_mem, secMk_one]
  have hgN : (secMk a X J y₁ h1 * secMk a X J x hxY * (secMk a X J y₁ h1)⁻¹) ^ (p ^ (m₁ + m₂)) = 1 := by
    rw [conj_pow, hbxN]; group
  have hcomm' : Commute (secMk a X J x' hx'Y) (secMk a X J w hwY) :=
    (hcentral _ hbx').symm
  have hωN : secMk a X J w hwY ^ (p ^ (m₁ + m₂)) = 1 := by
    rw [hB, hcomm'.mul_pow, hbx'N, one_mul] at hgN
    exact hgN
  have hω1 : secMk a X J w hwY = 1 := by
    have := (pow_gcd_eq_one (M := secB a X J) (a := secMk a X J w hwY)).mpr ⟨hωN, hr⟩
    rwa [hcop, pow_one] at this
  rw [hB, hω1, mul_one]
  exact secMk_mem_secX hx'

theorem SubData.zcontra {c : E4Ctx G z A a p X} {J : Subgroup A} (d : SubData c J)
    (h : Sl2Cl p (secZ a X J) (secX a X J) (secJ a X J))
    {y₁ y₂ : A} (hy₁ : y₁ ∈ J) (hy₁sq : y₁ * y₁ ≠ 1) (hy₁4 : (y₁ * y₁) * (y₁ * y₁) = 1)
    (hy₁z : a * y₁ * a⁻¹ = y₁⁻¹) (hy₂ : y₂ ∈ centralizer (J : Set A))
    (hy₂sq : y₂ * y₂ = y₁ * y₁) (hy₂z : a * y₂ * a⁻¹ = y₂⁻¹) : False := by
  have hcomm : y₁ * y₂ = y₂ * y₁ := Subgroup.mem_centralizer_iff.mp hy₂ y₁ hy₁
  have hu2 : (y₁ * y₂) * (y₁ * y₂) = 1 := by
    calc (y₁ * y₂) * (y₁ * y₂) = y₁ * (y₂ * y₁) * y₂ := by group
      _ = y₁ * (y₁ * y₂) * y₂ := by rw [← hcomm]
      _ = (y₁ * y₁) * (y₂ * y₂) := by group
      _ = 1 := by rw [hy₂sq]; exact hy₁4
  have hu1 : (y₁ * y₂)⁻¹ = y₁ * y₂ := inv_eq_of_mul_eq_one_right hu2
  have hua : (y₁ * y₂) * a = a * (y₁ * y₂) := by
    have h1 : a * (y₁ * y₂) * a⁻¹ = y₁ * y₂ := by
      calc a * (y₁ * y₂) * a⁻¹ = (a * y₁ * a⁻¹) * (a * y₂ * a⁻¹) := by group
        _ = y₁⁻¹ * y₂⁻¹ := by rw [hy₁z, hy₂z]
        _ = (y₂ * y₁)⁻¹ := by group
        _ = (y₁ * y₂)⁻¹ := by rw [hcomm]
        _ = y₁ * y₂ := hu1
    calc (y₁ * y₂) * a = (a * (y₁ * y₂) * a⁻¹) * a := by rw [h1]
      _ = a * (y₁ * y₂) := by group
  have hu : y₁ * y₂ ∈ normalizer (X : Set A) := c.inv _ hua
  have hu' : y₁⁻¹ * y₂⁻¹ ∈ normalizer (X : Set A) := by
    have : y₁⁻¹ * y₂⁻¹ = (y₁ * y₂)⁻¹ := by
      calc y₁⁻¹ * y₂⁻¹ = (y₂ * y₁)⁻¹ := by group
        _ = (y₁ * y₂)⁻¹ := by rw [hcomm]
    rw [this]
    exact inv_mem hu
  have hy₁Y : y₁ ∈ secY a X J := J_le_secY a X J hy₁
  have hnorm : secMk a X J y₁ hy₁Y ∈ normalizer ((secX a X J : Subgroup (secB a X J)) : Set (secB a X J)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      obtain ⟨x, hx, rfl⟩ := mem_secX_iff.mp hb
      exact zc_conj_mem d h hy₁ hy₂ hu hx
    · intro hb
      obtain ⟨x'', hx'', hbx⟩ := mem_secX_iff.mp hb
      have key := zc_conj_mem d h (inv_mem hy₁) (inv_mem hy₂) hu' hx''
      rw [secMk_inv hy₁Y] at key
      have : b = (secMk a X J y₁ hy₁Y)⁻¹ * (secMk a X J y₁ hy₁Y * b * (secMk a X J y₁ hy₁Y)⁻¹) *
          ((secMk a X J y₁ hy₁Y)⁻¹)⁻¹ := by group
      rw [this, hbx]
      exact key
  have hA4 := secB_Sig4A d.hyp
  have hyz : secZ a X J * secMk a X J y₁ hy₁Y * (secZ a X J)⁻¹ = (secMk a X J y₁ hy₁Y)⁻¹ := by
    have hzY := z_mem_secY a X J
    rw [← secMk_z (z := a) (X := X) (J := J), ← secMk_inv hzY, ← secMk_mul hzY hy₁Y,
      ← secMk_mul (mul_mem hzY hy₁Y) (inv_mem hzY), ← secMk_inv hy₁Y]
    exact secMk_congr hy₁z _ _
  have hy4 : (secMk a X J y₁ hy₁Y * secMk a X J y₁ hy₁Y) * (secMk a X J y₁ hy₁Y * secMk a X J y₁ hy₁Y) = 1 := by
    rw [← secMk_mul hy₁Y hy₁Y, ← secMk_mul (mul_mem hy₁Y hy₁Y) (mul_mem hy₁Y hy₁Y),
      secMk_congr hy₁4 _ (secY a X J).one_mem, secMk_one]
  have hsq := sq_eq_one_of_inverted_normalizes c.A4.prime c.A4.odd hA4.pgroup
    (z_mem_normalizer_of_sig4A hA4)
    (fun c' _ hc' => hA4.inv c' (Subgroup.mem_top c')
      (Subgroup.mem_centralizer_singleton_iff.mpr hc'))
    h.norm (secMk_mem_secJ hy₁) hnorm hyz hy4
  have hone : secMk a X J (y₁ * y₁) (mul_mem hy₁Y hy₁Y) = 1 := by
    rw [secMk_mul hy₁Y hy₁Y]; exact hsq
  have hmem := (secMk_eq_one_iff (mul_mem hy₁Y hy₁Y)).mp hone
  set t : ↥(secY a X J) := ⟨y₁ * y₁, mul_mem hy₁Y hy₁Y⟩ with ht
  have htt : t ^ 2 = 1 := by rw [pow_two]; exact Subtype.ext hy₁4
  have ht1 : t ≠ 1 := fun h1 => hy₁sq (congrArg Subtype.val h1)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf t = 2 := orderOf_eq_prime htt ht1
  have hdvd : 2 ∣ Nat.card (pPrimeCore 2 ↥(secY a X J)) := by
    have := orderOf_dvd_natCard (⟨t, hmem⟩ : ↥(pPrimeCore 2 ↥(secY a X J)))
    rwa [Subgroup.orderOf_mk, hord] at this
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥(secY a X J))) := N_odd
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

end

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
