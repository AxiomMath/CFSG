module

public import CFSG.GH74.Generic.S3.SL3Pair
public import CFSG.GH74.Generic.S3.L3Out
public import CFSG.GH74.Generic.S3.Rank5

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup
open CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices
open scoped MatrixGroups

section Abstract

variable {G : Type} [Group G]

theorem le_of_perfect_normalizing {N J : Subgroup G} {w e : G} [Group.IsPerfect ↥N]
    (hodd : Odd (Nat.card ↥(center ↥N))) (hPI : PerfectInInn (↥N ⧸ center ↥N))
    (hJN : J ≤ normalizer (N : Set G)) (hJq : IsQuasisimple ↥J)
    (hrk : NoCommInv (centralizer ({w} : Set G) ⊓ centralizer (N : Set G)))
    (hw : w * w = 1) (hw1 : w ≠ 1) (hNw : N ≤ centralizer ({w} : Set G))
    (hJw : J ≤ centralizer ({w} : Set G)) (heN : e ∈ N) (he2 : e * e = 1) (he1 : e ≠ 1)
    (hJe : ∀ j ∈ J, j * e = e * j)
    (hZ : ∀ z ∈ J, (∀ x ∈ J, x * z = z * x) → z = 1 ∨ z = e)
    (hQ : ∃ a ∈ J, ∃ b ∈ J, a * a = e ∧ b * b = e ∧ a * b = e * (b * a)) :
    J ≤ N := by
  have hK : (N.subgroupOf J).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := (mem_normalizer_iff.1 (hJN g.2) _).1 hn
    simpa using this
  rcases LocalCores.quasisimple_normal_subgroups hJq hK with htop | hcen
  · intro x hx
    have : (⟨x, hx⟩ : ↥J) ∈ N.subgroupOf J := by rw [htop]; trivial
    exact this
  · exfalso
    have : Group.IsPerfect ↥J := hJq.1
    have hJN1 : ∀ x ∈ J, x ∈ N → x = 1 ∨ x = e := by
      intro x hx hxN
      have hxc : (⟨x, hx⟩ : ↥J) ∈ center ↥J :=
        hcen (show (⟨x, hx⟩ : ↥J) ∈ N.subgroupOf J from hxN)
      refine hZ x hx (fun y hy => ?_)
      have := Subgroup.mem_center_iff.1 hxc ⟨y, hy⟩
      exact congrArg Subtype.val this
    have hwC : w ∈ centralizer ({w} : Set G) ⊓ centralizer (N : Set G) := by
      refine ⟨mem_centralizer_singleton_iff.2 rfl, ?_⟩
      exact mem_centralizer_iff.2 fun h hh => mem_centralizer_singleton_iff.1 (hNw hh)
    have key : ∀ x ∈ J, x * x = e → x⁻¹ * w ∈ N := by
      intro x hx hxx
      obtain ⟨m, hmN, hcm⟩ := exists_mul_centralizer_of_perfect N hPI hJN inferInstance x hx
      set c := x * m⁻¹ with hc
      have hcC : c ∈ centralizer ({w} : Set G) ⊓ centralizer (N : Set G) := by
        refine ⟨?_, hcm⟩
        exact (centralizer ({w} : Set G)).mul_mem (hJw hx)
          ((centralizer ({w} : Set G)).inv_mem (hNw hmN))
      have hxcm : x = c * m := by rw [hc]; group
      have hmc : m * c = c * m := mem_centralizer_iff.1 hcm m hmN
      have hcc : c * c * (m * m) = e := by
        calc c * c * (m * m) = c * (c * m) * m := by simp only [mul_assoc]
          _ = c * (m * c) * m := by rw [hmc]
          _ = (c * m) * (c * m) := by simp only [mul_assoc]
          _ = x * x := by rw [← hxcm]
          _ = e := hxx
      have hccN : c * c ∈ N := by
        have : c * c = e * (m * m)⁻¹ := eq_mul_inv_of_mul_eq hcc
        rw [this]
        exact N.mul_mem heN (N.inv_mem (N.mul_mem hmN hmN))
      have hccC : c * c ∈ centralizer (N : Set G) := (centralizer (N : Set G)).mul_mem hcm hcm
      have hz : (⟨c * c, hccN⟩ : ↥N) ∈ center ↥N := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (mem_centralizer_iff.1 hccC g g.2)
      set n := Nat.card ↥(center ↥N) with hn
      have hzpow : (⟨⟨c * c, hccN⟩, hz⟩ : ↥(center ↥N)) ^ n = 1 := pow_card_eq_one'
      have hccn : (c * c) ^ n = 1 := by
        have := congrArg (fun t : ↥(center ↥N) => ((t : ↥N) : G)) hzpow
        simpa using this
      obtain ⟨k, hk⟩ := hodd
      set y := c ^ n with hy
      have hyy : y * y = 1 := by
        rw [hy, ← (Commute.refl c).mul_pow, hccn]
      have hyC : y ∈ centralizer ({w} : Set G) ⊓ centralizer (N : Set G) :=
        Subgroup.pow_mem _ hcC n
      have hyN : x⁻¹ * y ∈ N := by
        have hy' : y = c * (c * c) ^ k := by
          rw [hy, hk, pow_succ', pow_mul, sq]
        have : x⁻¹ * y = m⁻¹ * (c * c) ^ k := by
          rw [hy', hc]; group
        rw [this]
        exact N.mul_mem (N.inv_mem hmN) (N.pow_mem hccN k)
      have hy1 : y ≠ 1 := by
        intro h1
        rw [h1, mul_one] at hyN
        have hxN : x ∈ N := by simpa using N.inv_mem hyN
        rcases hJN1 x hx hxN with h | h
        · rw [h, one_mul] at hxx
          exact he1 hxx.symm
        · rw [h, he2] at hxx
          exact he1 hxx.symm
      have hcomm : y * w = w * y := mem_centralizer_singleton_iff.1 hyC.1
      rcases hrk y hyC w hwC hyy hw hcomm with h | h | h
      · exact absurd h hy1
      · exact absurd h hw1
      · rw [← h]; exact hyN
    obtain ⟨a, ha, b, hb, haa, hbb, hab⟩ := hQ
    have ha' := key a ha haa
    have hb' := key b hb hbb
    have hba : b⁻¹ * a ∈ N := by
      have : b⁻¹ * a = (b⁻¹ * w) * (a⁻¹ * w)⁻¹ := by group
      rw [this]
      exact N.mul_mem hb' (N.inv_mem ha')
    have hbaJ : b⁻¹ * a ∈ J := J.mul_mem (J.inv_mem hb) ha
    have hbinv : b⁻¹ = e * b := by
      apply inv_eq_of_mul_eq_one_right
      calc b * (e * b) = (b * e) * b := by rw [mul_assoc]
        _ = (e * b) * b := by rw [hJe b hb]
        _ = e * (b * b) := by rw [mul_assoc]
        _ = 1 := by rw [hbb, he2]
    have hsq : (b⁻¹ * a) * (b⁻¹ * a) = e := by
      rw [hbinv]
      have hea : a * e = e * a := hJe a ha
      have heb : b * e = e * b := hJe b hb
      calc e * b * a * (e * b * a) = e * b * (a * e) * b * a := by simp only [mul_assoc]
        _ = e * b * (e * a) * b * a := by rw [hea]
        _ = e * (b * e) * a * b * a := by simp only [mul_assoc]
        _ = e * (e * b) * a * b * a := by rw [heb]
        _ = (e * e) * b * (a * b) * a := by simp only [mul_assoc]
        _ = b * (e * (b * a)) * a := by rw [he2, one_mul, hab]
        _ = (b * e) * b * a * a := by simp only [mul_assoc]
        _ = e * (b * b) * (a * a) := by rw [heb]; simp only [mul_assoc]
        _ = e := by rw [hbb, haa, he2, one_mul]
    rcases hJN1 _ hbaJ hba with h | h
    · rw [h, one_mul] at hsq
      exact he1 hsq.symm
    · rw [h, he2] at hsq
      exact he1 hsq.symm

end Abstract

section SL2

variable {G : Type} [Group G]

theorem IsSL2Comp.isQuasisimple {F : Type*} [Field F] {w₁ e : G} {J : Subgroup G}
    (h : IsSL2Comp F w₁ e J) : IsQuasisimple ↥J :=
  LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h.1) h.2.1.1

theorem sl2_facts {F : Type} [Field F] [Finite F] (hF : ringChar F ≠ 2) {J : Subgroup G}
    (φ : SL(2, F) ≃* J) {e : G} (heJ : e ∈ J) (hcen : ∀ j ∈ J, j * e = e * j) (he1 : e ≠ 1) :
    (∀ z ∈ J, (∀ x ∈ J, x * z = z * x) → z = 1 ∨ z = e) ∧
      ∃ a ∈ J, ∃ b ∈ J, a * a = e ∧ b * b = e ∧ a * b = e * (b * a) := by
  have hcenter := (sl2_img_eq_z hF φ heJ hcen he1).1
  refine ⟨fun z hz hzc => hcenter z hz fun x hx => (hzc x hx).symm, ?_⟩
  have hneg1 : (-1 : SL(2, F)) ≠ 1 := by
    intro h
    have h' := congrArg (fun A : SL(2, F) => ((A : Matrix (Fin 2) (Fin 2) F) 0 0)) h
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one] at h'
    simp at h'
    exact Ring.neg_one_ne_one_of_char_ne_two hF h'
  have hc : ∀ b ∈ J, ((φ (-1) : J) : G) * b = b * ((φ (-1) : J) : G) := by
    intro b hb
    obtain ⟨B, hB⟩ := φ.surjective ⟨b, hb⟩
    have hBneg : (-1 : SL(2, F)) * B = B * (-1 : SL(2, F)) := by
      apply Subtype.ext
      simp
    have := congrArg (fun A : J => (A : G)) (congrArg φ hBneg)
    simp only [map_mul, Subgroup.coe_mul, hB] at this
    exact this
  have hneg : ((φ (-1) : J) : G) = e := by
    rcases hcenter _ (φ (-1)).2 hc with h1 | h2
    · exfalso
      have h3 : (φ (-1) : J) = 1 := Subtype.ext h1
      exact hneg1 (φ.injective (h3.trans (map_one φ).symm))
    · exact h2
  obtain ⟨a, b, hab⟩ := (odd_field_two_dimensional_quaternion_matrices hF).1
  obtain ⟨hdI, hdJ, hII, hJJ, hIJ, -⟩ := (odd_field_two_dimensional_quaternion_matrices hF).2 a b hab
  let I : SL(2, F) := ⟨quatI F, hdI⟩
  let Jm : SL(2, F) := ⟨quatJ a b, hdJ⟩
  have hI2 : I * I = -1 := by
    apply Subtype.ext
    simpa using hII
  have hJ2 : Jm * Jm = -1 := by
    apply Subtype.ext
    simpa using hJJ
  have hIJ' : I * Jm = (-1 : SL(2, F)) * (Jm * I) := by
    apply Subtype.ext
    simpa using hIJ
  refine ⟨((φ I : J) : G), (φ I).2, ((φ Jm : J) : G), (φ Jm).2, ?_, ?_, ?_⟩
  · rw [← Subgroup.coe_mul, ← map_mul, hI2, hneg]
  · rw [← Subgroup.coe_mul, ← map_mul, hJ2, hneg]
  · rw [← Subgroup.coe_mul, ← map_mul, hIJ', map_mul, Subgroup.coe_mul, hneg, map_mul,
      Subgroup.coe_mul]

end SL2

theorem b_S3_J_in_Iw : B_S3_J_in_Iw := by
  intro G _ _ hG t p f v w Iv Iw Ivw P V v₁ hconf F _ _ hF e he J hJ
  have C := hconf.conf
  have hIq : IsQuasisimple ↥Iw := C.comp_w.1.isQuasisimple
  have : Group.IsPerfect ↥Iw := hIq.1
  have h5 : 5 ≤ p ^ f := C.prime.2.2
  have hPI := perfectInInn_of_lieModel C.tag h5 C.model_w
  have hJw : J ≤ centralizer ({w} : Set G) :=
    hJ.1.trans (Subgroup.centralizer_le (by simp))
  have hJN : J ≤ normalizer (Iw : Set G) := hJw.trans C.comp_w.le_normalizer
  have hQ := sylow_inf_centralizer C.sylow_w C.comp_w.le_normalizer
  have hrk : NoCommInv (centralizer ({w} : Set G) ⊓ centralizer (Iw : Set G)) :=
    noCommInv_of_sylow hQ (noCommInv_of_cyclic C.Q_cyc)
  have hw1 : w ≠ 1 := fun h => by
    have := C.w_inv
    rw [h, orderOf_one] at this
    omega
  have hF2 : ringChar F ≠ 2 := ringChar_ne_two_of_card_pow C.prime.1 C.prime.2.1 hF
  obtain ⟨hZ, hQ'⟩ := sl2_facts hF2 (Classical.choice hJ.iso) hJ.mem (fun j hj => (hJ.commute j hj).2)
    he.2
  exact le_of_perfect_normalizing C.odd_w hPI hJN hJ.isQuasisimple hrk hconf.setup.w_sq hw1
    C.comp_w.1.1 hJw (hconf.hVIw he.1) (hconf.setup.V_sq e he.1) he.2
    (fun j hj => (hJ.commute j hj).2) hZ hQ'

end CFSG.GH74.Generic.S3
