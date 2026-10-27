module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecGenLift
public import CFSG.LocalAnalysis.OddStandard.AltStdSecGenOdd

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup

section Lift

variable {N M : Type*} [Group N] [Finite N] [Group M]

theorem exists_perfect_lift (π : N →* M) (K : Subgroup M) (hK : ⁅K, K⁆ = K)
    (hKr : K ≤ π.range) : ∃ Q : Subgroup N, Q.map π = K ∧ ⁅Q, Q⁆ = Q := by
  have hne : ∃ Y : Subgroup N, Y.map π = K :=
    ⟨K.comap π, by rw [Subgroup.map_comap_eq]; exact inf_eq_right.2 hKr⟩
  obtain ⟨Q, hQ, hmin⟩ := (wellFounded_lt (α := Subgroup N)).has_min {Y | Y.map π = K} hne
  refine ⟨Q, hQ, ?_⟩
  have h1 : (⁅Q, Q⁆).map π = K := by rw [Subgroup.map_commutator, hQ, hK]
  have h2 : ⁅Q, Q⁆ ≤ Q := by
    rw [Subgroup.commutator_le]
    intro g hg h hh
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  exact eq_of_le_of_not_lt h2 (hmin _ h1)

end Lift

section Main

variable {N : Type*} [Group N] [Finite N]

theorem exists_wreath_lift {O R B : Subgroup N} [O.Normal] (hOodd : Odd (Nat.card O))
    (hRO : R ≤ O) (hRc : R ≤ Subgroup.center N) {z : N} (hz : z * z = 1)
    (hCz : ∀ u ∈ O, z * u * z⁻¹ = u → u ∈ R) {m : ℕ} (hm : 8 ≤ m)
    {K : Subgroup (N ⧸ O)} (eK : K ≃* alternatingGroup (Fin m))
    (hKK : ∀ a ∈ K, ∀ b ∈ K, a * ((z : N ⧸ O) * b * (z : N ⧸ O)⁻¹) =
      ((z : N ⧸ O) * b * (z : N ⧸ O)⁻¹) * a)
    (hBperf : ⁅B, B⁆ = B) (hBz : ∀ b ∈ B, z * b * z⁻¹ = b)
    (hB : ∀ g : N ⧸ O, g ∈ B.map (QuotientGroup.mk' O) ↔
      ∃ k ∈ K, g = k * ((z : N ⧸ O) * k * (z : N ⧸ O)⁻¹)) :
    ∃ (Q : Subgroup N) (ψ : B →* N), Q.map (QuotientGroup.mk' O) = K ∧ ⁅Q, Q⁆ = Q ∧
      Q ⊓ O = ⊥ ∧ (∀ q ∈ Q, ∀ u ∈ O, q * u = u * q) ∧
      (∀ a ∈ Q, ∀ x ∈ zConjSub z Q, a * x = x * a) ∧ Q ⊓ zConjSub z Q = ⊥ ∧ (∀ b, ψ b ∈ Q) ∧
      Function.Injective ψ ∧ (∀ b, ψ b * (z * ψ b * z⁻¹) = b) := by
  classical
  set π : N →* N ⧸ O := QuotientGroup.mk' O with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective O
  have hOodd' : ∀ x ∈ O, Odd (orderOf x) := fun x hx =>
    hOodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hx)
  have hKperf : ⁅K, K⁆ = K := by
    have hc := (isQuasisimple_of_alt (by omega : 5 ≤ m) eK).1
    exact Subgroup.isPerfect_iff.1 ⟨hc⟩
  obtain ⟨Q, hQmap, hQperf⟩ := exists_perfect_lift π K hKperf (by
    rw [MonoidHom.range_eq_top.2 hπsurj]; exact le_top)
  have hQz : ∀ a ∈ Q, ∀ b ∈ Q, a * (z * b * z⁻¹) * a⁻¹ * (z * b * z⁻¹)⁻¹ ∈ O := by
    intro a ha b hb
    have haK : π a ∈ K := hQmap ▸ ⟨a, ha, rfl⟩
    have hbK : π b ∈ K := hQmap ▸ ⟨b, hb, rfl⟩
    rw [← QuotientGroup.eq_one_iff]
    show π (a * (z * b * z⁻¹) * a⁻¹ * (z * b * z⁻¹)⁻¹) = 1
    have := hKK _ haK _ hbK
    simp only [map_mul, map_inv]
    rw [show π z = (z : N ⧸ O) from rfl] 
    rw [this]; group
  have hQO := perfect_centralizes_oddCore hOodd' hRO hRc hz hCz hQperf hQz
  have hQQz := perfect_commute_zConjSub hQperf hQO hQz
  have hQbot : Q ⊓ O = ⊥ := by
    let πQ : ↥Q →* ↥K := (π.comp Q.subtype).codRestrict K (fun q => by
      rw [← hQmap]; exact ⟨q, q.2, rfl⟩)
    let π' : ↥Q →* alternatingGroup (Fin m) := eK.toMonoidHom.comp πQ
    have hπ' : Function.Surjective π' := by
      intro a
      have h1 : (eK.symm a : N ⧸ O) ∈ Q.map π := by rw [hQmap]; exact (eK.symm a).2
      obtain ⟨q, hq, hqe⟩ := h1
      refine ⟨⟨q, hq⟩, ?_⟩
      apply eK.symm.injective
      apply Subtype.ext
      simpa [π', πQ] using hqe
    have hker_le : ∀ q : ↥Q, q ∈ π'.ker → (q : N) ∈ O := by
      intro q hq
      have h1 : eK (πQ q) = 1 := hq
      have h2 : πQ q = 1 := by simpa using h1
      have h3 : π q = 1 := congrArg Subtype.val h2
      exact (QuotientGroup.eq_one_iff (q : N)).1 h3
    have hZc : π'.ker ≤ Subgroup.center ↥Q := by
      intro q hq
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact hQO g g.2 q (hker_le q hq)
    have hodd' : Odd (Nat.card π'.ker) := by
      let ι : π'.ker →* O := MonoidHom.codRestrict ((Q.subtype).comp π'.ker.subtype) O
        (fun q => hker_le q.1 q.2)
      have hι : Function.Injective ι := by
        intro a b hab
        have h1 : ((ι a : O) : N) = ((ι b : O) : N) := congrArg Subtype.val hab
        exact Subtype.ext (Subtype.ext h1)
      exact hOodd.of_dvd_nat (Subgroup.card_dvd_of_injective ι hι)
    have : Group.IsPerfect ↥Q := Subgroup.isPerfect_iff.2 hQperf
    have hbot := ker_eq_bot_of_perfect_odd_central_cover hm π' hπ' hZc hodd'
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxQ, hxO⟩ := hx
    have hxk : (⟨x, hxQ⟩ : ↥Q) ∈ π'.ker := by
      show eK (πQ ⟨x, hxQ⟩) = 1
      have : πQ ⟨x, hxQ⟩ = 1 := Subtype.ext ((QuotientGroup.eq_one_iff x).2 hxO)
      rw [this, map_one]
    rw [hbot] at hxk
    have := congrArg Subtype.val (Subgroup.mem_bot.1 hxk)
    exact Subgroup.mem_bot.2 this
  have hQQzbot : Q ⊓ zConjSub z Q = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgQ, hgz⟩ := hg
    have hπg : π g ∈ K := hQmap ▸ ⟨g, hgQ, rfl⟩
    have hcen : (⟨π g, hπg⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro k
      obtain ⟨q, hq, hqk⟩ : (k : N ⧸ O) ∈ Q.map π := by rw [hQmap]; exact k.2
      apply Subtype.ext
      show (k : N ⧸ O) * π g = π g * k
      rw [← hqk, ← map_mul, ← map_mul, hQQz q hq g hgz]
    rw [center_eq_bot_of_alt (by omega : 4 ≤ m) eK] at hcen
    have h1 : π g = 1 := congrArg Subtype.val (Subgroup.mem_bot.1 hcen)
    have hgO : g ∈ O := (QuotientGroup.eq_one_iff g).1 h1
    have : g ∈ Q ⊓ O := ⟨hgQ, hgO⟩
    rwa [hQbot] at this
  let πQ : ↥Q →* ↥K := (π.comp Q.subtype).codRestrict K (fun q => by
    rw [← hQmap]; exact ⟨q, q.2, rfl⟩)
  have hπQbij : Function.Bijective πQ := by
    constructor
    · intro a b hab
      have h1 : π (a : N) = π (b : N) := congrArg Subtype.val hab
      have h2 : ((a : N)⁻¹ * (b : N)) ∈ O := by
        rw [← QuotientGroup.eq_one_iff]
        show π ((a : N)⁻¹ * (b : N)) = 1
        rw [map_mul, map_inv, h1]; group
      have h3 : ((a : N)⁻¹ * (b : N)) ∈ Q ⊓ O := ⟨Q.mul_mem (Q.inv_mem a.2) b.2, h2⟩
      rw [hQbot] at h3
      have h4 : (a : N)⁻¹ * (b : N) = 1 := h3
      exact Subtype.ext (inv_mul_eq_one.1 h4)
    · intro k
      have h1 : (k : N ⧸ O) ∈ Q.map π := by rw [hQmap]; exact k.2
      obtain ⟨q, hq, hqk⟩ := h1
      exact ⟨⟨q, hq⟩, Subtype.ext hqk⟩
  let eQ : ↥Q ≃* ↥K := MulEquiv.ofBijective πQ hπQbij
  set zq : N ⧸ O := (z : N ⧸ O) with hzq
  let δ : ↥K →* N ⧸ O := MonoidHom.mk' (fun k => (k : N ⧸ O) * (zq * k * zq⁻¹)) (fun a b => by
    have hc : (b : N ⧸ O) * (zq * (a : N ⧸ O) * zq⁻¹) = (zq * (a : N ⧸ O) * zq⁻¹) * b :=
      hKK b b.2 a a.2
    show ((a * b : ↥K) : N ⧸ O) * (zq * ((a * b : ↥K) : N ⧸ O) * zq⁻¹) =
      ((a : N ⧸ O) * (zq * a * zq⁻¹)) * ((b : N ⧸ O) * (zq * b * zq⁻¹))
    rw [Subgroup.coe_mul]
    calc ((a : N ⧸ O) * b) * (zq * ((a : N ⧸ O) * b) * zq⁻¹)
        = (a : N ⧸ O) * ((b : N ⧸ O) * (zq * a * zq⁻¹)) * (zq * b * zq⁻¹) := by group
      _ = (a : N ⧸ O) * ((zq * a * zq⁻¹) * b) * (zq * b * zq⁻¹) := by rw [hc]
      _ = ((a : N ⧸ O) * (zq * a * zq⁻¹)) * ((b : N ⧸ O) * (zq * b * zq⁻¹)) := by group)
  have hδinj : Function.Injective δ := by
    intro a b hab
    have hker : ∀ k : ↥K, δ k = 1 → k = 1 := by
      intro k hk
      have h1 : (k : N ⧸ O) * (zq * k * zq⁻¹) = 1 := hk
      have h2 : zq * (k : N ⧸ O) * zq⁻¹ = (k : N ⧸ O)⁻¹ := eq_inv_of_mul_eq_one_right h1
      have hcen : k ∈ Subgroup.center ↥K := by
        rw [Subgroup.mem_center_iff]
        intro g
        apply Subtype.ext
        have := hKK g g.2 k k.2
        rw [h2] at this
        show (g : N ⧸ O) * k = k * g
        have h3 : (g : N ⧸ O) * (k : N ⧸ O)⁻¹ = (k : N ⧸ O)⁻¹ * g := this
        calc (g : N ⧸ O) * k = k * ((k : N ⧸ O)⁻¹ * g) * k := by group
          _ = k * ((g : N ⧸ O) * (k : N ⧸ O)⁻¹) * k := by rw [← h3]
          _ = k * g := by group
      rw [center_eq_bot_of_alt (by omega : 4 ≤ m) eK] at hcen
      exact hcen
    have : δ (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
    exact inv_mul_eq_one.1 (hker _ this)
  have hδrange : δ.range = B.map π := by
    ext g
    rw [hB]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, k.2, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
  let eδ : ↥K ≃* ↥δ.range := MonoidHom.ofInjective hδinj
  let πB : ↥B →* ↥δ.range := (π.comp B.subtype).codRestrict δ.range (fun b => by
    rw [hδrange]; exact ⟨b, b.2, rfl⟩)
  let κ : ↥B →* ↥K := eδ.symm.toMonoidHom.comp πB
  let ψ : ↥B →* N := Q.subtype.comp (eQ.symm.toMonoidHom.comp κ)
  have hπψ : ∀ b : ↥B, π (ψ b) = (κ b : N ⧸ O) := by
    intro b
    have h1 : πQ (eQ.symm (κ b)) = κ b := eQ.apply_symm_apply (κ b)
    exact congrArg Subtype.val h1
  have hδκ : ∀ b : ↥B, δ (κ b) = π b := by
    intro b
    have h1 : eδ (κ b) = πB b := eδ.apply_symm_apply (πB b)
    exact congrArg Subtype.val h1
  have hψQ : ∀ b : ↥B, ψ b ∈ Q := fun b => (eQ.symm (κ b)).2
  have hcomm : ∀ a b : ↥B, ψ a * (z * ψ b * z⁻¹) = (z * ψ b * z⁻¹) * ψ a := fun a b =>
    hQQz _ (hψQ a) _ (mem_zConjSub.2 ⟨ψ b, hψQ b, rfl⟩)
  have hconjconj : ∀ g : N, z * (z * g * z⁻¹) * z⁻¹ = g := fun g => by
    calc z * (z * g * z⁻¹) * z⁻¹ = (z * z) * g * (z * z)⁻¹ := by group
      _ = g := by rw [hz]; group
  let xh : ↥B →* N := MonoidHom.mk' (fun b => ψ b * (z * ψ b * z⁻¹)) (fun a b => by
    have hc := hcomm b a
    show ψ (a * b) * (z * ψ (a * b) * z⁻¹) =
      (ψ a * (z * ψ a * z⁻¹)) * (ψ b * (z * ψ b * z⁻¹))
    rw [map_mul]
    calc ψ a * ψ b * (z * (ψ a * ψ b) * z⁻¹)
        = ψ a * (ψ b * (z * ψ a * z⁻¹)) * (z * ψ b * z⁻¹) := by group
      _ = ψ a * ((z * ψ a * z⁻¹) * ψ b) * (z * ψ b * z⁻¹) := by rw [hc]
      _ = (ψ a * (z * ψ a * z⁻¹)) * (ψ b * (z * ψ b * z⁻¹)) := by group)
  have hxπ : ∀ b : ↥B, π (xh b) = π b := by
    intro b
    show π (ψ b * (z * ψ b * z⁻¹)) = π b
    rw [map_mul, map_mul, map_mul, map_inv, hπψ]
    exact hδκ b
  have hxz : ∀ b : ↥B, z * xh b * z⁻¹ = xh b := by
    intro b
    show z * (ψ b * (z * ψ b * z⁻¹)) * z⁻¹ = ψ b * (z * ψ b * z⁻¹)
    calc z * (ψ b * (z * ψ b * z⁻¹)) * z⁻¹
        = (z * ψ b * z⁻¹) * (z * (z * ψ b * z⁻¹) * z⁻¹) := by group
      _ = (z * ψ b * z⁻¹) * ψ b := by rw [hconjconj]
      _ = ψ b * (z * ψ b * z⁻¹) := (hcomm b b).symm
  have hdef : ∀ b : ↥B, (b : N)⁻¹ * xh b ∈ R := by
    intro b
    apply hCz
    · rw [← QuotientGroup.eq_one_iff]
      show π ((b : N)⁻¹ * xh b) = 1
      rw [map_mul, map_inv, hxπ]; group
    · have hbz : z * (b : N)⁻¹ * z⁻¹ = (b : N)⁻¹ := by
        calc z * (b : N)⁻¹ * z⁻¹ = (z * (b : N) * z⁻¹)⁻¹ := by group
          _ = (b : N)⁻¹ := by rw [hBz b b.2]
      calc z * ((b : N)⁻¹ * xh b) * z⁻¹ = (z * (b : N)⁻¹ * z⁻¹) * (z * xh b * z⁻¹) := by group
        _ = (b : N)⁻¹ * xh b := by rw [hbz, hxz]
  have hxo : ∀ b : ↥B, xh b = ((b : N)⁻¹ * xh b) * (b : N) := by
    intro b
    have hcen := Subgroup.mem_center_iff.1 (hRc (hdef b)) (b : N)
    calc xh b = (b : N) * ((b : N)⁻¹ * xh b) := by group
      _ = ((b : N)⁻¹ * xh b) * (b : N) := hcen
  have hT : B ≤ (MonoidHom.eqLocus xh B.subtype).map B.subtype := by
    refine le_of_comm_mem hBperf (fun a ha c hc => ?_)
    refine ⟨⟨a, ha⟩ * ⟨c, hc⟩ * ⟨a, ha⟩⁻¹ * ⟨c, hc⟩⁻¹, ?_, rfl⟩
    show xh (⟨a, ha⟩ * ⟨c, hc⟩ * ⟨a, ha⟩⁻¹ * ⟨c, hc⟩⁻¹) = a * c * a⁻¹ * c⁻¹
    obtain ⟨wa, hwaR, hwa⟩ : ∃ w ∈ R, xh ⟨a, ha⟩ = w * a := ⟨_, hdef ⟨a, ha⟩, hxo ⟨a, ha⟩⟩
    obtain ⟨wc, hwcR, hwc⟩ : ∃ w ∈ R, xh ⟨c, hc⟩ = w * c := ⟨_, hdef ⟨c, hc⟩, hxo ⟨c, hc⟩⟩
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hwa, hwc,
      comm_mul_central_left (hRc hwaR), comm_mul_central_right (hRc hwcR)]
  have hxeq : ∀ b : ↥B, xh b = (b : N) := by
    intro b
    obtain ⟨b', hb', hbb⟩ := hT b.2
    have : b' = b := Subtype.ext hbb
    rw [← this]; exact hb'
  refine ⟨Q, ψ, hQmap, hQperf, hQbot, hQO, hQQz, hQQzbot, hψQ, ?_, ?_⟩
  · intro a b hab
    have h1 : xh a = xh b := by
      show ψ a * (z * ψ a * z⁻¹) = ψ b * (z * ψ b * z⁻¹)
      rw [hab]
    rw [hxeq a, hxeq b] at h1
    exact Subtype.ext h1
  · intro b
    exact hxeq b

end Main

end CFSG.OddStandard.AltStdSec
