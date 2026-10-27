module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpE4Psi
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpE4Two

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section

variable {A : Type} [Group A]

theorem conj_mem_centralizer {J : Subgroup A} {x w : A} (hx : x ∈ normalizer (J : Set A))
    (hw : w ∈ centralizer (J : Set A)) : x * w * x⁻¹ ∈ centralizer (J : Set A) := by
  rw [Subgroup.mem_centralizer_iff]
  intro j hj
  have hj' : x⁻¹ * j * x⁻¹⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (inv_mem hx) j).mp hj
  have h1 := Subgroup.mem_centralizer_iff.mp hw _ hj'
  simp only [inv_inv] at h1
  calc j * (x * w * x⁻¹) = x * ((x⁻¹ * j * x) * w) * x⁻¹ := by group
    _ = x * (w * (x⁻¹ * j * x)) * x⁻¹ := by rw [h1]
    _ = (x * w * x⁻¹) * j := by group

theorem centralizes_of_comm_central [Finite A] {J : Subgroup A} (hJ : IsComponent J) {g : A}
    (hg : g ∈ normalizer (J : Set A)) (h : ∀ j ∈ J, ⁅g, j⁆ ∈ centralizer (J : Set A)) :
    g ∈ centralizer (J : Set A) := by
  let S : Subgroup A :=
    { carrier := {x | x ∈ normalizer (J : Set A) ∧ ∀ j ∈ J, ⁅x, j⁆ ∈ centralizer (J : Set A)}
      one_mem' := ⟨one_mem _, fun j _ => by simp⟩
      mul_mem' := by
        rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
        refine ⟨mul_mem hx hy, fun j hj => ?_⟩
        have e : ⁅x * y, j⁆ = (x * ⁅y, j⁆ * x⁻¹) * ⁅x, j⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact mul_mem (conj_mem_centralizer hx (hy' j hj)) (hx' j hj)
      inv_mem' := by
        rintro x ⟨hx, hx'⟩
        refine ⟨inv_mem hx, fun j hj => ?_⟩
        have e : ⁅x⁻¹, j⁆ = x⁻¹ * (⁅x, j⁆)⁻¹ * x⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact conj_mem_centralizer (inv_mem hx) (inv_mem (hx' j hj)) }
  have hgS : g ∈ S := ⟨hg, h⟩
  have hzS : zpowers g ≤ S := Subgroup.zpowers_le.mpr hgS
  have hperf : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.mp hJ.1.1
  have hle : ⁅J, zpowers g⁆ ≤ centralizer (J : Set A) := by
    rw [Subgroup.commutator_le]
    intro j hj w hw
    have := (hzS hw).2 j hj
    rw [← commutatorElement_inv w j]
    exact inv_mem this
  have hbot := comm_eq_bot_of_central hperf (Subgroup.zpowers_le.mpr hg) hle
  rw [Subgroup.mem_centralizer_iff]
  intro j hj
  have h1 : ⁅j, g⁆ ∈ ⁅J, zpowers g⁆ := Subgroup.commutator_mem_commutator hj (Subgroup.mem_zpowers g)
  rw [hbot] at h1
  exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp h1)

end

section

variable {G : Type} [Group G] {z : G} {k : Kind}
variable {A : Type} [Group A] [Finite A] {a : A} {p : ℕ} {X J : Subgroup A}

omit [Finite A] in
theorem no_p_elements_of_normal_comm {p : ℕ} (hop : pCore p A = ⊥) {M : Subgroup A} (hM : M.Normal)
    (hcomm : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x) : ∀ m ∈ M, ∀ k : ℕ, m ^ (p ^ k) = 1 → m = 1 := by
  intro t0 ht0 m0 hm0
  let S : Subgroup A :=
    { carrier := {t | t ∈ M ∧ ∃ m : ℕ, t ^ (p ^ m) = 1}
      one_mem' := ⟨M.one_mem, 0, by simp⟩
      mul_mem' := by
        rintro a b ⟨haT, m₁, h₁⟩ ⟨hbT, m₂, h₂⟩
        refine ⟨M.mul_mem haT hbT, m₁ + m₂, ?_⟩
        have hc : Commute a b := hcomm a haT b hbT
        rw [hc.mul_pow]
        have e1 : a ^ (p ^ (m₁ + m₂)) = 1 := by
          rw [pow_add, pow_mul, h₁, one_pow]
        have e2 : b ^ (p ^ (m₁ + m₂)) = 1 := by
          rw [add_comm, pow_add, pow_mul, h₂, one_pow]
        rw [e1, e2, one_mul]
      inv_mem' := by
        rintro a ⟨haT, m, h⟩
        exact ⟨M.inv_mem haT, m, by rw [inv_pow, h, inv_one]⟩ }
  have hSn : S.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨hnT, m, hm⟩ := hn
    exact ⟨hM.conj_mem n hnT g, m, by rw [conj_pow, hm]; group⟩
  have hSp : IsPGroup p ↥S := by
    rintro ⟨s, hs⟩
    obtain ⟨m, hm⟩ := hs.2
    exact ⟨m, Subtype.ext hm⟩
  have hmem : S ∈ {M : Subgroup A | M.Normal ∧ IsPGroup p ↥M} := ⟨hSn, hSp⟩
  have hSle : S ≤ pCore p A := le_sSup hmem
  rw [hop] at hSle
  exact Subgroup.mem_bot.mp (hSle ⟨ht0, m0, hm0⟩)

theorem secPsi_ker_coprime {p : ℕ} [Fact p.Prime] (h : SubHyp a p X J) (hJn : J.Normal)
    (hop : pCore p A = ⊥) : Nat.Coprime p (Nat.card (secPsi a X J).ker) := by
  have hker_le : (secPsi a X J).ker ≤ pPrimeCore 2 ↥J :=
    SubAbs.le_pPrimeCore_of_odd (G := ↥J) _ (secPsi_ker_odd h)
  have hMn : (pPrimeCoreOf 2 J).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hg : g ∈ normalizer ((pPrimeCoreOf 2 J : Subgroup A) : Set A) :=
      subsec_normalizer_le_normalizer_pPrimeCoreOf J
        (by rw [Subgroup.mem_normalizer_iff]; intro y; exact ⟨fun hy => hJn.conj_mem y hy g,
          fun hy => by simpa [mul_assoc] using hJn.conj_mem _ hy g⁻¹⟩)
    exact (Subgroup.mem_normalizer_iff.mp hg n).mp hn
  have hMc : ∀ x ∈ pPrimeCoreOf 2 J, ∀ y ∈ pPrimeCoreOf 2 J, x * y = y * x := by
    intro x hx y hy
    have hxJ : x ∈ J := Subgroup.map_subtype_le _ hx
    have hxc : y ∈ centralizer (J : Set A) := pPrimeCoreOf_le_centralizer h.comp.1 hy
    exact Subgroup.mem_centralizer_iff.mp hxc x hxJ
  have hno := no_p_elements_of_normal_comm hop hMn hMc
  by_contra hcop
  have hdvd : p ∣ Nat.card (secPsi a X J).ker := by
    rcases (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).not.mp hcop |> not_not.mp with hd
    exact hd
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hu1 : u ^ p = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  have hmem : ((u : ↥J) : A) ∈ pPrimeCoreOf 2 J := ⟨(u : ↥J), hker_le u.2, rfl⟩
  have hpow : ((u : ↥J) : A) ^ (p ^ 1) = 1 := by
    have := congrArg (fun t : (secPsi a X J).ker => (((t : ↥J) : A))) hu1
    simpa using this
  have h1 := hno _ hmem 1 hpow
  have : u = 1 := Subtype.ext (Subtype.ext h1)
  rw [this, orderOf_one] at hu
  exact (Fact.out : p.Prime).one_lt.ne hu

theorem SubData.secY_le_normalizer {c : E4Ctx G z A a p X} (d : SubData c J) :
    secY a X J ≤ normalizer (J : Set A) :=
  sup_le (sup_le le_normalizer d.XJ) (Subgroup.zpowers_le.mpr d.zJ)

theorem SubData.mem_sup_centralizer_of_B {c : E4Ctx G z A a p X} (d : SubData c J)
    (h : secZ a X J ∈ secJ a X J ⊔
      centralizer ((secJ a X J : Subgroup (secB a X J)) : Set (secB a X J))) :
    a ∈ J ⊔ centralizer (J : Set A) := by
  have hcomm : ∀ b ∈ secJ a X J, ∀ b' ∈
      centralizer ((secJ a X J : Subgroup (secB a X J)) : Set (secB a X J)), b * b' = b' * b :=
    fun b hb b' hb' => Subgroup.mem_centralizer_iff.mp hb' b hb
  obtain ⟨k, hk, c', hc', hkc⟩ := exists_mul_of_mem_sup hcomm h
  obtain ⟨j, hj, rfl⟩ := mem_secJ_iff.mp hk
  obtain ⟨y, hyY, rfl⟩ := secMk_surjective c'
  have hjY : j ∈ secY a X J := J_le_secY a X J hj
  have hzY : a ∈ secY a X J := z_mem_secY a X J
  have hjyY : j * y ∈ secY a X J := mul_mem hjY hyY
  have h1 : secMk a X J a hzY = secMk a X J (j * y) hjyY := by
    rw [secMk_mul hjY hyY]
    exact hkc.symm
  have hn := (secMk_eq_iff hzY hjyY).mp h1
  set n : ↥(secY a X J) := (⟨a, hzY⟩ : ↥(secY a X J))⁻¹ * ⟨j * y, hjyY⟩ with hndef
  have hnA : (n : A) = a⁻¹ * (j * y) := rfl
  set c₀ : A := y * (n : A)⁻¹ with hc₀def
  have hc₀Y : c₀ ∈ secY a X J := mul_mem hyY (inv_mem n.2)
  have hac : a = j * c₀ := by rw [hc₀def, hnA]; group
  have hmk : secMk a X J c₀ hc₀Y = secMk a X J y hyY := by
    have h2 : secMk a X J c₀ hc₀Y = secMk a X J y hyY * (secMk a X J (n : A) n.2)⁻¹ := rfl
    have h3 : secMk a X J (n : A) n.2 = 1 := (secMk_eq_one_iff n.2).mpr hn
    rw [h2, h3, inv_one, mul_one]
  have hc₀N : c₀ ∈ normalizer (J : Set A) := d.secY_le_normalizer hc₀Y
  have hc₀C : c₀ ∈ centralizer (J : Set A) := by
    refine centralizes_of_comm_central d.comp hc₀N (fun j' hj' => ?_)
    have hj'Y : j' ∈ secY a X J := J_le_secY a X J hj'
    have hwJ : ⁅c₀, j'⁆ ∈ J := by
      have := (Subgroup.mem_normalizer_iff.mp hc₀N j').mp hj'
      simp only [commutatorElement_def]
      exact mul_mem this (inv_mem hj')
    have hwY : ⁅c₀, j'⁆ ∈ secY a X J := J_le_secY a X J hwJ
    have hone : secMk a X J ⁅c₀, j'⁆ hwY = 1 := by
      have e : secMk a X J ⁅c₀, j'⁆ hwY = secMk a X J c₀ hc₀Y * secMk a X J j' hj'Y *
          (secMk a X J c₀ hc₀Y)⁻¹ * (secMk a X J j' hj'Y)⁻¹ := rfl
      rw [e, hmk]
      have hcm : secMk a X J j' hj'Y * secMk a X J y hyY = secMk a X J y hyY * secMk a X J j' hj'Y :=
        hcomm _ (secMk_mem_secJ hj') _ hc'
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
      exact hcm.symm
    have hker : (⟨⁅c₀, j'⁆, hwJ⟩ : ↥J) ∈ (secPsi a X J).ker :=
      (secPsi_eq_one_iff _).mpr ((secMk_eq_one_iff hwY).mp hone)
    have hcen := Subgroup.mem_center_iff.mp (secPsi_ker_central d.hyp hker)
    rw [Subgroup.mem_centralizer_iff]
    intro j'' hj''
    exact congrArg Subtype.val (hcen ⟨j'', hj''⟩)
  rw [hac]
  exact Subgroup.mul_mem_sup hj hc₀C

end

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
