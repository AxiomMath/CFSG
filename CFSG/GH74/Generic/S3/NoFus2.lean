module

public import CFSG.GH74.Generic.S3.LyTrans
public import CFSG.GH74.Generic.S3.LxySplit

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open CFSG.GH74.Filter.ClassicalOdd (Q8)

section Comp

variable {G : Type} [Group G] [Finite G] {t : StatedLieTag} {p f : ℕ} {x y : G} {Iw Iv : Subgroup G}

theorem NbrData.x_notin_Iw (hnd : NbrData G t p f x y Iw Iv) : x ∉ Iw := by
  intro hx
  exact not_central_involution_of_odd hnd.odd_w hx hnd.x_sq hnd.x_ne_one
    (fun i hi => mem_centralizer_singleton_iff.1 (hnd.Iw_le hi))

theorem NbrData.commute_conj_Iv (hnd : NbrData G t p f x y Iw Iv) (hIv : IsCompC Iv y) {g : G}
    (hg : g * x * g⁻¹ = y) : ∀ i ∈ Iv, ∀ b ∈ Iw, (g⁻¹ * i * g) * b = b * (g⁻¹ * i * g) := by
  have hxg : g⁻¹ * y * g⁻¹⁻¹ = x := by rw [← hg]; group
  have hH : IsCompC (Iv.map (MulAut.conj g⁻¹).toMonoidHom) x := by
    have := hIv.map_conj g⁻¹
    rwa [hxg] at this
  rcases hH.eq_or_commute hnd.comp_w.1 with h | h
  · exfalso
    apply hnd.x_notin_Iw
    rw [← h]
    exact ⟨y, hnd.y_Iv, by simp; rw [← hg]; group⟩
  · intro i hi b hb
    exact h _ ⟨i, hi, by simp⟩ b hb

end Comp

section Mod4

variable {G : Type} [Group G] [Finite G] {t : StatedLieTag} {p f : ℕ} {x y : G} {Iw Iv : Subgroup G}

theorem not_commutative_q8 : ¬ ∀ a b : Q8, a * b = b * a := by
  intro h
  have := h (QuaternionGroup.a 1) (QuaternionGroup.xa 0)
  revert this
  decide

theorem NbrData.mod_four_of_quaternion {K : Subgroup (CentralizerBar x)} (hset : S3Setup G x K)
    (hnd : NbrData G t p f x y Iw Iv) (himg : imgBar x Iw = K) (ψ : Q8 →* G)
    (hψ : Function.Injective ψ) (hψx : ∀ a, ψ a ∈ centralizer ({x} : Set G))
    (hψc : ∀ a, ∀ b ∈ Iw, ψ a * b = b * ψ a) :
    (t = .PSL ∧ p ^ f % 4 = 3) ∨ (t = .PSU ∧ p ^ f % 4 = 1) := by
  by_contra hcon
  have hodd : p ^ f % 2 = 1 := Nat.odd_iff.1 ((hnd.prime.1.odd_of_ne_two hnd.prime.2.1).pow)
  obtain ⟨⟨p₀, f₀, -, -, -, hmodelK₀⟩, -⟩ := hset.shape
  have hKcen : center ↥K = ⊥ := center_eq_bot_of_quasisimple_lieModel_L3 hset.comp.1 hmodelK₀
  have hKnt : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hset.comp.1
  have hmodelK : LieModel ↥K t 3 p f := hnd.lxy_lieModel_K himg hKcen hKnt
  have he : ∃ p' f' : ℕ, (LieModel ↥K .PSL 3 p' f' ∧ p' ^ f' % 4 = 1) ∨
      (LieModel ↥K .PSU 3 p' f' ∧ p' ^ f' % 4 = 3) := by
    rcases hnd.tag with rfl | rfl
    · refine ⟨p, f, Or.inl ⟨hmodelK, ?_⟩⟩
      by_contra h
      exact hcon (Or.inl ⟨rfl, by omega⟩)
    · refine ⟨p, f, Or.inr ⟨hmodelK, ?_⟩⟩
      by_contra h
      exact hcon (Or.inr ⟨rfl, by omega⟩)
  have hX : Gen4 (CentralizerBar x) := gen4_centralizerBar hset.gen4 x
  let φ : Q8 →* CentralizerBar x := (proj x).comp (ψ.codRestrict (centralizer ({x} : Set G)) hψx)
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hodd' := proj_odd x (ψ.codRestrict (centralizer ({x} : Set G)) hψx a) ha
    have hQp : IsPGroup 2 Q8 := IsPGroup.of_card (n := 3) (by rw [Nat.card_eq_fintype_card]; decide)
    obtain ⟨k, hk⟩ := hQp a
    have h2 : orderOf (ψ.codRestrict (centralizer ({x} : Set G)) hψx a) ∣ 2 ^ k := by
      have : (ψ.codRestrict (centralizer ({x} : Set G)) hψx a) ^ (2 ^ k) = 1 := by
        rw [← map_pow, hk, map_one]
      exact orderOf_dvd_of_pow_eq_one this
    have hcop : Nat.Coprime (2 ^ k) (orderOf (ψ.codRestrict (centralizer ({x} : Set G)) hψx a)) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd')
    have h3 : orderOf (ψ.codRestrict (centralizer ({x} : Set G)) hψx a) = 1 :=
      Nat.Coprime.eq_one_of_dvd hcop.symm h2
    have h4 := orderOf_eq_one_iff.1 h3
    have h5 : ψ a = 1 := congrArg Subtype.val h4
    exact hψ (h5.trans (map_one ψ).symm)
  have hQp : IsPGroup 2 Q8 := IsPGroup.of_card (n := 3) (by rw [Nat.card_eq_fintype_card]; decide)
  set P : Subgroup (CentralizerBar x) := φ.range with hP
  have hP2 : IsPGroup 2 ↥P := hQp.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hKP : ∀ k ∈ K, ∀ q ∈ P, k * q = q * k := by
    intro k hk q hq
    obtain ⟨a, rfl⟩ := hq
    rw [← himg] at hk
    obtain ⟨g', hg', rfl⟩ := mem_imgBar.1 hk
    show proj x g' * φ a = φ a * proj x g'
    simp only [φ, MonoidHom.comp_apply]
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (hψc a g' hg').symm
  have hinf : K ⊓ P = ⊥ := by
    rw [eq_bot_iff]
    rintro k ⟨hkK, hkP⟩
    have hcent : (⟨k, hkK⟩ : ↥K) ∈ center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro k'
      apply Subtype.ext
      exact (hKP k' k'.2 k hkP)
    rw [hKcen, Subgroup.mem_bot] at hcent
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hcent
  have hcyc : IsCyclic ↥P := cyclic_of_rankCertified hX (rankCertified_two_of_eps he) hKP hinf hP2
  apply not_commutative_q8
  intro a b
  let _inst : CommGroup ↥P := IsCyclic.commGroup
  have h1 : φ.rangeRestrict a * φ.rangeRestrict b = φ.rangeRestrict b * φ.rangeRestrict a :=
    mul_comm _ _
  rw [← map_mul, ← map_mul] at h1
  exact (MonoidHom.rangeRestrict_injective_iff.2 hφinj) h1

end Mod4

end CFSG.GH74.Generic.S3
