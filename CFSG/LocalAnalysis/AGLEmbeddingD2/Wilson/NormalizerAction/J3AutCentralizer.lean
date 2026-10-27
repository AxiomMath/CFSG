module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3A6Classes
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3OuterCard
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3CentralizerStructure
public import CFSG.Sporadic.SmallOddCore.J3Aut
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG CFSG.Blueprint CFSG.RankThree.PartTwo.Sec21 CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier CFSG.Sporadic

section Main


set_option linter.unusedSectionVars false

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem centralizer_perfect_eq_zpowers {Q : Type*} [Group Q] (e : Q ≃* NativeSporadic.J3) {x : Q}
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hC : Nat.card (centralizer ({x} : Set Q)) = 1080)
    {I : Subgroup Q} (hIC : I ≤ centralizer ({x} : Set Q)) (hI : ⁅I, I⁆ = I)
    (hI360 : Nat.card I = 360) (hIA6 : Nonempty (↥I ≃* alternatingGroup (Fin 6))) :
    centralizer (I : Set Q) = zpowers x := by
  obtain ⟨eI⟩ := hIA6
  have hZI := center_eq_bot_of_equiv_alt6 I eI
  have hfinQ : Finite Q := Finite.of_equiv _ e.symm.toEquiv
  set Y : Subgroup Q := centralizer (I : Set Q) with hY
  have hxY : x ∈ Y := by
    rw [hY, mem_centralizer_iff]
    intro i hi
    exact mem_centralizer_singleton_iff.1 (hIC hi)
  have hYI : ∀ y ∈ Y, y ∈ I → y = 1 := by
    intro y hy hyI
    have : (⟨y, hyI⟩ : ↥I) ∈ center ↥I := by
      rw [Subgroup.mem_center_iff]
      intro z
      exact Subtype.ext (mem_centralizer_iff.1 hy z z.2)
    rw [hZI, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  obtain ⟨y₁, hy₁I, hy₁o⟩ : ∃ y₁ ∈ I, orderOf y₁ = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hd : 3 ∣ Nat.card I := by rw [hI360]; norm_num
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 hd
    exact ⟨(z : Q), z.2, by rw [Subgroup.orderOf_coe]; exact hz⟩
  have hy₁3 : y₁ ^ 3 = 1 := by rw [← hy₁o]; exact pow_orderOf_eq_one y₁
  have hy₁1 : y₁ ≠ 1 := by
    intro h; rw [h, orderOf_one] at hy₁o; omega
  have hC243 := j3_a6_threeElements_class e hx3 hx1 hC I hIC hI y₁ hy₁I hy₁1 hy₁3
  have hYle : Y ≤ centralizer ({y₁} : Set Q) := by
    intro y hy
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.1 hy y₁ hy₁I).symm
  have hYdvd : Nat.card Y ∣ 243 := hC243 ▸ Subgroup.card_dvd_of_le hYle
  have hY3 : IsPGroup 3 Y := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
      (show Nat.card Y ∣ 3 ^ 5 by simpa using hYdvd)
    exact IsPGroup.of_card hk
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hCYx : ∀ y ∈ Y, y * x = x * y → y ∈ zpowers x := by
    set CY : Subgroup Q := Y ⊓ centralizer ({x} : Set Q) with hCY
    have hxCY : zpowers x ≤ CY := by
      rw [Subgroup.zpowers_le]
      exact ⟨hxY, mem_centralizer_singleton_iff.2 rfl⟩
    let f : ↥CY × ↥I → ↥(centralizer ({x} : Set Q)) := fun p =>
      ⟨(p.1 : Q) * p.2, by
        rw [mem_centralizer_singleton_iff]
        have h1 : (p.1 : Q) * x = x * p.1 := mem_centralizer_singleton_iff.1 p.1.2.2
        have h2 : (p.2 : Q) * x = x * p.2 := mem_centralizer_singleton_iff.1 (hIC p.2.2)
        calc (p.1 : Q) * p.2 * x = p.1 * (p.2 * x) := by group
          _ = p.1 * (x * p.2) := by rw [h2]
          _ = (p.1 * x) * p.2 := by group
          _ = (x * p.1) * p.2 := by rw [h1]
          _ = x * (p.1 * p.2) := by group⟩
    have hfinj : Function.Injective f := by
      rintro ⟨y₁, i₁⟩ ⟨y₂, i₂⟩ h
      have h' : (y₁ : Q) * i₁ = y₂ * i₂ := congrArg Subtype.val h
      have hmem : ((y₂ : Q)⁻¹ * y₁) ∈ I := by
        have : (y₂ : Q)⁻¹ * y₁ = i₂ * (i₁ : Q)⁻¹ := by
          calc (y₂ : Q)⁻¹ * y₁ = (y₂ : Q)⁻¹ * (y₁ * i₁) * (i₁ : Q)⁻¹ := by group
            _ = (y₂ : Q)⁻¹ * (y₂ * i₂) * (i₁ : Q)⁻¹ := by rw [h']
            _ = i₂ * (i₁ : Q)⁻¹ := by group
        rw [this]; exact I.mul_mem i₂.2 (I.inv_mem i₁.2)
      have hmemY : ((y₂ : Q)⁻¹ * y₁) ∈ Y := Y.mul_mem (Y.inv_mem y₂.2.1) y₁.2.1
      have h1 := hYI _ hmemY hmem
      have hy : (y₂ : Q) = y₁ := inv_mul_eq_one.1 h1
      have hyy : y₁ = y₂ := Subtype.ext hy.symm
      have hii : i₁ = i₂ := Subtype.ext (mul_left_cancel (by rw [h', hy]))
      rw [hyy, hii]
    have hcard : Nat.card ↥CY * 360 ≤ 1080 := by
      calc Nat.card ↥CY * 360 = Nat.card (↥CY × ↥I) := by
            rw [Nat.card_prod, hI360]
        _ ≤ Nat.card ↥(centralizer ({x} : Set Q)) := Nat.card_le_card_of_injective f hfinj
        _ = 1080 := hC
    have hcard3 : Nat.card ↥CY ≤ 3 := by omega
    have hzCY : zpowers x = CY := by
      refine Subgroup.eq_of_le_of_card_ge hxCY ?_
      rw [Nat.card_zpowers, hxo]; exact hcard3
    intro y hy hcomm
    have : y ∈ CY := ⟨hy, mem_centralizer_singleton_iff.2 hcomm⟩
    rwa [← hzCY] at this
  haveI : Nontrivial ↥Y := ⟨⟨⟨x, hxY⟩, 1, fun h => hx1 (congrArg Subtype.val h)⟩⟩
  haveI : Finite ↥Y := inferInstance
  have hcenY : Nontrivial ↥(Subgroup.center ↥Y) := hY3.center_nontrivial
  obtain ⟨z, hz⟩ : ∃ z : ↥(Subgroup.center ↥Y), orderOf z = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hpg : IsPGroup 3 ↥(Subgroup.center ↥Y) := hY3.to_subgroup _
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hpg
    have hn1 : n ≠ 0 := by
      rintro rfl
      have h1 : 1 < Nat.card ↥(Subgroup.center ↥Y) := Finite.one_lt_card_iff_nontrivial.2 hcenY
      rw [hn] at h1
      norm_num at h1
    have hd : 3 ∣ Nat.card ↥(Subgroup.center ↥Y) := by
      rw [hn]; exact dvd_pow_self 3 hn1
    exact exists_prime_orderOf_dvd_card' 3 hd
  set zQ : Q := (((z : ↥Y)) : Q) with hzQ
  have hzY : zQ ∈ Y := (z : ↥Y).2
  have hzcen : ∀ y ∈ Y, y * zQ = zQ * y := by
    intro y hy
    have := Subgroup.mem_center_iff.1 z.2 ⟨y, hy⟩
    exact congrArg Subtype.val this
  have hzo : orderOf zQ = 3 := by
    rw [hzQ, Subgroup.orderOf_coe, Subgroup.orderOf_coe]; exact hz
  have hz3 : zQ ^ 3 = 1 := by rw [← hzo]; exact pow_orderOf_eq_one zQ
  have hz1 : zQ ≠ 1 := by intro h; rw [h, orderOf_one] at hzo; omega
  have hzx : zQ ∈ zpowers x := hCYx zQ hzY (hzcen x hxY).symm
  have hxz : x ∈ zpowers zQ := by
    have hle : zpowers zQ ≤ zpowers x := Subgroup.zpowers_le.2 hzx
    have heq : zpowers zQ = zpowers x := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hzo, hxo]
    rw [heq]; exact Subgroup.mem_zpowers x
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hxz
  have hxcen : ∀ y ∈ Y, y * x = x * y := by
    intro y hy
    rw [← hm]
    exact (Commute.zpow_right (show Commute y zQ from hzcen y hy) m).eq
  apply le_antisymm
  · intro y hy
    exact hCYx y hy (hxcen y hy)
  · rw [Subgroup.zpowers_le]; exact hxY

theorem sq_mem_j3P_of_mem_j3R {r : Equiv.Perm (Fin 6156)} (hr : r ∈ j3R) :
    r ^ 2 ∈ j3P := by
  obtain ⟨hU2, -, hUP, hmapu, -, hRmem, -⟩ :=
    ctuc_j3_normalizing_involution_permutation_model
  by_cases hrP : r ∈ j3P
  · exact j3P.pow_mem hrP 2
  · have h1 : r * j3u ∈ j3P :=
      ((hRmem r).1 hr).resolve_left hrP
    have hu : j3u * (r * j3u) *
        j3u⁻¹ ∈ j3P := by
      rw [← hmapu]
      exact ⟨r * j3u, h1, rfl⟩
    have hUU : j3u * j3u = 1 := by
      rw [← sq, hU2]
    have : r ^ 2 = (r * j3u) *
        (j3u * (r * j3u) *
          j3u⁻¹) := by
      calc r ^ 2 = r * (j3u * j3u) * r := by
            rw [hUU, mul_one, sq]
        _ = _ := by group
    rw [this]
    exact j3P.mul_mem h1 hu

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem aut_eq_conj_of_trivial_on_perfect
    {Q : Type*} [Group Q] (e : Q ≃* NativeSporadic.J3) {x : Q}
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hC : Nat.card (centralizer ({x} : Set Q)) = 1080)
    {I : Subgroup Q} (hIC : I ≤ centralizer ({x} : Set Q)) (hI : ⁅I, I⁆ = I)
    (hI360 : Nat.card I = 360) (hIA6 : Nonempty (↥I ≃* alternatingGroup (Fin 6)))
    (σ : MulAut Q) (hσ : ∀ i ∈ I, σ i = i) : ∃ n : ℤ, σ = MulAut.conj (x ^ n) := by
  have hY := centralizer_perfect_eq_zpowers e hx3 hx1 hC hIC hI hI360 hIA6
  obtain ⟨eR, heR, himg, -⟩ := ctuc_j3_full_automorphism_permutation_model
  set ψ : Q ≃* ↥j3P := e.trans Item228CensusProof.j3CarrierEquiv with hψ
  set σ' : MulAut ↥j3P := MulAut.congr ψ σ with hσ'
  set r : ↥j3R := eR.symm σ' with hr
  have hrapp : ∀ p : ↥j3P, ((σ' p : ↥j3P) : Equiv.Perm (Fin 6156)) =
      (r : Equiv.Perm (Fin 6156)) * p * (r : Equiv.Perm (Fin 6156))⁻¹ := by
    intro p
    have := heR r p
    rw [hr, MulEquiv.apply_symm_apply] at this
    exact this
  have hσ'app : ∀ y : Q, σ' (ψ y) = ψ (σ y) := by
    intro y; simp [hσ', MulAut.congr_apply]
  have hrI : ∀ i ∈ I, (r : Equiv.Perm (Fin 6156)) * (ψ i : Equiv.Perm (Fin 6156)) =
      (ψ i : Equiv.Perm (Fin 6156)) * (r : Equiv.Perm (Fin 6156)) := by
    intro i hi
    have h1 := hrapp (ψ i)
    rw [hσ'app, hσ i hi] at h1
    exact mul_inv_eq_iff_eq_mul.1 h1.symm
  have hfix : ∀ q' : Equiv.Perm (Fin 6156), ∀ hq' : q' ∈ j3P,
      (∀ i ∈ I, q' * (ψ i : Equiv.Perm (Fin 6156)) = (ψ i : Equiv.Perm (Fin 6156)) * q') →
      ∃ n : ℤ, ψ (x ^ n) = ⟨q', hq'⟩ := by
    intro q' hq' hcomm
    have hmem : ψ.symm ⟨q', hq'⟩ ∈ centralizer (I : Set Q) := by
      rw [mem_centralizer_iff]
      intro i hi
      apply ψ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subtype.ext (hcomm i hi).symm
    rw [hY] at hmem
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hmem
    exact ⟨n, by rw [hn, MulEquiv.apply_symm_apply]⟩
  by_cases hrP : (r : Equiv.Perm (Fin 6156)) ∈ j3P
  · obtain ⟨n, hn⟩ := hfix r hrP hrI
    refine ⟨n, ?_⟩
    ext y
    apply ψ.injective
    rw [← hσ'app, MulAut.conj_apply, map_mul, map_mul, map_inv, hn]
    apply Subtype.ext
    rw [hrapp]
    simp
  · exfalso
    have hr2 : (r : Equiv.Perm (Fin 6156)) ^ 2 ∈ j3P := sq_mem_j3P_of_mem_j3R r.2
    have hr2I : ∀ i ∈ I, (r : Equiv.Perm (Fin 6156)) ^ 2 * (ψ i : Equiv.Perm (Fin 6156)) =
        (ψ i : Equiv.Perm (Fin 6156)) * (r : Equiv.Perm (Fin 6156)) ^ 2 := by
      intro i hi
      have h := hrI i hi
      calc (r : Equiv.Perm (Fin 6156)) ^ 2 * ψ i = r * (r * ψ i) := by rw [sq, mul_assoc]
        _ = r * (ψ i * r) := by rw [h]
        _ = (r * ψ i) * r := by rw [mul_assoc]
        _ = (ψ i * r) * r := by rw [h]
        _ = ψ i * r ^ 2 := by rw [sq, mul_assoc]
    obtain ⟨n, hn⟩ := hfix _ hr2 hr2I
    have hr6 : (r : Equiv.Perm (Fin 6156)) ^ 6 = 1 := by
      have hxn3 : (x ^ n) ^ 3 = 1 := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
      have h5 : ψ (x ^ n) ^ 3 = 1 := by rw [← map_pow, hxn3, map_one]
      have h4 := congrArg (fun w : ↥j3P => (w : Equiv.Perm (Fin 6156))) h5
      rw [hn] at h4
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at h4
      rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul]
      exact h4
    set τ : Equiv.Perm (Fin 6156) := (r : Equiv.Perm (Fin 6156)) ^ 3 with hτ
    have hτR : τ ∈ j3R := j3R.pow_mem r.2 3
    have hτP : τ ∉ j3P := by
      intro hτP
      apply hrP
      have : (r : Equiv.Perm (Fin 6156)) = τ * ((r : Equiv.Perm (Fin 6156)) ^ 2)⁻¹ := by
        rw [hτ]; group
      rw [this]
      exact j3P.mul_mem hτP (j3P.inv_mem hr2)
    have hτ2 : τ ^ 2 = 1 := by rw [hτ, ← pow_mul]; exact hr6
    have hτ1 : τ ≠ 1 := by
      intro h; apply hτP; rw [h]; exact j3P.one_mem
    have hτo : orderOf τ = 2 := orderOf_eq_prime hτ2 hτ1
    have hτI : ∀ i ∈ I, τ * (ψ i : Equiv.Perm (Fin 6156)) = (ψ i : Equiv.Perm (Fin 6156)) * τ := by
      intro i hi
      have h := hrI i hi
      rw [hτ]
      exact (Commute.pow_left (show Commute (r : Equiv.Perm (Fin 6156)) (ψ i) from h) 3).eq
    have hcard := card_centralizer_outer_involution hτR hτo hτP
    have hinj : Function.Injective (j3P.subtype.comp ψ.toMonoidHom) :=
      Subtype.val_injective.comp ψ.injective
    have hIbar : Nat.card (I.map (j3P.subtype.comp ψ.toMonoidHom)) = 360 := by
      rw [Subgroup.card_map_of_injective hinj, hI360]
    have hle : I.map (j3P.subtype.comp ψ.toMonoidHom) ≤
        j3P ⊓ centralizer ({τ} : Set (Equiv.Perm (Fin 6156))) := by
      rintro _ ⟨i, hi, rfl⟩
      refine ⟨(ψ i).2, ?_⟩
      show ((ψ i : ↥j3P) : Equiv.Perm (Fin 6156)) ∈ centralizer ({τ} : Set (Equiv.Perm (Fin 6156)))
      rw [mem_centralizer_singleton_iff]
      exact (hτI i hi).symm
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hcard, hIbar] at hdvd
    norm_num at hdvd

end Main

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
