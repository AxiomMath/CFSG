module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionOddQuotientStrongEmbedding

public section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.Open CFSG.BenderSuzuki CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q]

omit [Finite Q] in
theorem local_point_unique_containment_image (f : G →* Q)
    (hf : Function.Surjective f) (hodd : Odd (Nat.card f.ker))
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z) :
    ∀ qg : Q, f z ∈ rightConjugate (H.map f) qg ↔ qg ∈ H.map f := by
  have hz : IsInvolution z :=
    ⟨(orderOf_eq_prime_iff.mp h.distinguished_order).2,
      (orderOf_eq_prime_iff.mp h.distinguished_order).1⟩
  have hfz := involution_image_of_odd_kernel f hodd hz
  intro qg
  constructor
  · intro hzright
    obtain ⟨g, hg⟩ := hf qg
    have hzmap : f z ∈ (rightConjugate H g).map f := by
      rw [odd_quotient_rightConjugate_map, hg]
      exact hzright
    obtain ⟨s, hsright, hs, hfs⟩ :=
      involution_lift_in_subgroup_of_odd_kernel f hodd (rightConjugate H g) hfz hzmap
    obtain ⟨n, hn, hzn⟩ := involutions_kernel_conjugate f hodd hz hs hfs.symm
    have hznright : rightConjugateElem z n ∈ rightConjugate H g := hzn.symm ▸ hsright
    obtain ⟨a, haH, hag⟩ := Subgroup.mem_map.mp hznright
    change g⁻¹ * a * (g⁻¹)⁻¹ = rightConjugateElem z n at hag
    rw [inv_inv] at hag
    change rightConjugateElem a g = rightConjugateElem z n at hag
    have heq : rightConjugateElem a (g * n⁻¹) = z := by
      rw [← rightConjugateElem_comp, hag]
      simp only [rightConjugateElem]
      group
    have hzright' : z ∈ rightConjugate H (g * n⁻¹) := by
      rw [← heq]
      exact rightConjugateElem_mem_rightConjugate haH
    have hmember := (h.unique_containment (g * n⁻¹)).mp hzright'
    have himage := Subgroup.mem_map_of_mem f hmember
    rw [map_mul, map_inv, show f n = 1 from hn, inv_one, mul_one, hg] at himage
    exact himage
  · intro hqg
    let K := H.map f
    have hzK : f z ∈ K := Subgroup.mem_map_of_mem f h.distinguished_mem
    rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨qg * f z * qg⁻¹, K.mul_mem (K.mul_mem hqg hzK) (K.inv_mem hqg), ?_⟩
    change qg⁻¹ * (qg * f z * qg⁻¹) * (qg⁻¹)⁻¹ = f z
    group

omit [Finite Q] in
theorem local_involution_point_hull_image (f : G →* Q)
    (hf : Function.Surjective f) (hodd : Odd (Nat.card f.ker))
    {z u : G} (hz : IsInvolution z) (hu : IsInvolution u) :
    (localInvolutionPointHull z u).map f =
      localInvolutionPointHull (f z) (f u) := by
  unfold localInvolutionPointHull
  rw [f.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨w, ⟨hwclass, hwC⟩, rfl⟩
    have hwI : IsInvolution w := by
      have hw := order_two_of_mem_pointClass
        (orderOf_eq_prime hz.sq_eq_one hz.ne_one) hwclass
      exact ⟨(orderOf_eq_prime_iff.mp hw).2, (orderOf_eq_prime_iff.mp hw).1⟩
    exact ⟨(involution_point_class_image_iff f hf hodd hz hwI).mpr hwclass,
      Subgroup.mem_centralizer_singleton_iff.mpr
        ((show Commute w u from Subgroup.mem_centralizer_singleton_iff.mp hwC).map f)⟩
  · rintro ⟨hyclass, hyC⟩
    have hyI : IsInvolution y := by
      have hfz := involution_image_of_odd_kernel f hodd hz
      have hy := order_two_of_mem_pointClass
        (orderOf_eq_prime hfz.sq_eq_one hfz.ne_one) hyclass
      exact ⟨(orderOf_eq_prime_iff.mp hy).2, (orderOf_eq_prime_iff.mp hy).1⟩
    obtain ⟨w, hw, hfw, hwu⟩ := commuting_involution_lift_of_odd_kernel f hf hodd hu hyI
      (Subgroup.mem_centralizer_singleton_iff.mp hyC)
    have hwclass : w ∈ involutionPointClass z :=
      (involution_point_class_image_iff f hf hodd hz hw).mp (hfw.symm ▸ hyclass)
    exact ⟨w, ⟨hwclass, Subgroup.mem_centralizer_singleton_iff.mpr hwu⟩, hfw⟩

theorem local_involution_point_embedding_image (f : G →* Q)
    (hf : Function.Surjective f) (hodd : Odd (Nat.card f.ker))
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (hproper : H.map f ≠ ⊤) :
    InvolutionPointLocalEmbedding (H.map f) (f z) := by
  have hz : IsInvolution z :=
    ⟨(orderOf_eq_prime_iff.mp h.distinguished_order).2,
      (orderOf_eq_prime_iff.mp h.distinguished_order).1⟩
  have hfz := involution_image_of_odd_kernel f hodd hz
  have huniq := local_point_unique_containment_image f hf hodd h
  refine ⟨hproper, Subgroup.mem_map_of_mem f h.distinguished_mem,
    orderOf_eq_prime hfz.sq_eq_one hfz.ne_one, huniq, ?_⟩
  intro uq huq huqz hescape
  have huqI : IsInvolution uq :=
    ⟨(orderOf_eq_prime_iff.mp huq).2, (orderOf_eq_prime_iff.mp huq).1⟩
  obtain ⟨u, hu, hfu, huz⟩ := commuting_involution_lift_of_odd_kernel f hf hodd hz huqI huqz
  have hescapeG : ¬ Subgroup.centralizer ({u} : Set G) ≤ H := by
    intro hle
    apply hescape
    rw [← hfu, ← involution_centralizer_image f hf hodd hu]
    exact Subgroup.map_mono hle
  let L := localInvolutionPointHull z u
  let Lq := localInvolutionPointHull (f z) uq
  have hL : L.map f = Lq := by
    simpa only [L, Lq, hfu] using local_involution_point_hull_image f hf hodd hz hu
  let fq : L →* Lq := (f.comp L.subtype).codRestrict Lq
    (fun x => hL ▸ Subgroup.mem_map_of_mem f x.property)
  have hfq : Function.Surjective fq := by
    rintro ⟨y, hy⟩
    rw [← hL] at hy
    obtain ⟨x, hx, hfx⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext hfx⟩
  have hoddq : Odd (Nat.card fq.ker) := by
    have hker : fq.ker = (f.comp L.subtype).ker := by
      ext x
      change (⟨f x, _⟩ : Lq) = 1 ↔ f x = 1
      exact Subtype.ext_iff
    rw [hker]
    exact odd_kernel_subgroup_restriction f hodd L
  let M := H.subgroupOf L
  let Mq := (H.map f).subgroupOf Lq
  have hMqproper : Mq ≠ ⊤ := by
    intro htop
    have hlocalle : Lq ≤ H.map f := by
      intro y hy
      have hm : (⟨y, hy⟩ : Lq) ∈ Mq := by rw [htop]; exact Subgroup.mem_top _
      exact hm
    apply hescape
    intro x hxC
    have hzlocal : rightConjugateElem (f z) x ∈ Lq := by
      apply mem_localInvolutionPointHull ⟨x, rfl⟩
      have hzC : f z ∈ Subgroup.centralizer ({uq} : Set Q) :=
        Subgroup.mem_centralizer_singleton_iff.mpr huqz.symm
      have hc := (Subgroup.centralizer ({uq} : Set Q)).mul_mem
        ((Subgroup.centralizer ({uq} : Set Q)).mul_mem
          ((Subgroup.centralizer ({uq} : Set Q)).inv_mem hxC) hzC) hxC
      exact Subgroup.mem_centralizer_singleton_iff.mp hc
    have hzH := hlocalle hzlocal
    have hzright : f z ∈ rightConjugate (H.map f) x⁻¹ := by
      have hm := rightConjugateElem_mem_rightConjugate (g := x⁻¹) hzH
      simpa only [rightConjugateElem, inv_inv, mul_assoc, mul_inv_cancel,
        mul_inv_cancel_left, mul_one] using hm
    exact (H.map f).inv_mem_iff.mp ((huniq x⁻¹).mp hzright)
  have hMMq : M.map fq ≤ Mq := by
    rintro y ⟨x, hx, rfl⟩
    exact Subgroup.mem_map_of_mem f hx
  have himageproper : M.map fq ≠ ⊤ := by
    intro htop
    exact hMqproper (top_unique (htop ▸ hMMq))
  have hM := native_strong_embedding_of_order_conditions
    (h.local_embedding u (orderOf_eq_prime hu.sq_eq_one hu.ne_one) huz hescapeG)
  have hMimage := strong_embedding_image_of_odd_kernel fq hfq hoddq hM himageproper
  have hMq := strong_embedding_proper_overgroup hMimage hMMq hMqproper
  have hlocal := order_strong_embedding_of_native hMq
  simpa only [Mq, Lq] using hlocal

theorem local_involution_point_embedding_odd_quotient
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (N : Subgroup G) [N.Normal] (hNodd : Odd (Nat.card N)) (hproper : H ⊔ N ≠ ⊤) :
    InvolutionPointLocalEmbedding (H.map (QuotientGroup.mk' N))
      (QuotientGroup.mk' N z) := by
  let f := QuotientGroup.mk' N
  have hodd : Odd (Nat.card f.ker) := by
    simpa only [f, QuotientGroup.ker_mk'] using hNodd
  have himageproper : H.map f ≠ ⊤ := by
    intro htop
    apply hproper
    have heq := Subgroup.comap_map_eq f H
    rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at heq
    exact heq.symm
  exact local_involution_point_embedding_image f (QuotientGroup.mk'_surjective N) hodd h
    himageproper

theorem local_involution_point_embedding_odd_quotient_central_sylow
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (N : Subgroup G) [N.Normal] (hNodd : Odd (Nat.card N)) (hproper : H ⊔ N ≠ ⊤)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hcentral : ∀ s ∈ (S : Subgroup G), Commute z s) :
    InvolutionPointLocalEmbedding (H.map (QuotientGroup.mk' N))
        (QuotientGroup.mk' N z) ∧
      ∃ T : Sylow 2 (G ⧸ N),
        (T : Subgroup (G ⧸ N)) = (S : Subgroup G).map (QuotientGroup.mk' N) ∧
        QuotientGroup.mk' N z ∈ (T : Subgroup (G ⧸ N)) ∧
        ∀ t ∈ (T : Subgroup (G ⧸ N)), Commute (QuotientGroup.mk' N z) t :=
  ⟨local_involution_point_embedding_odd_quotient h N hNodd hproper,
    central_sylow_two_image (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
      S hzS hcentral⟩

end CFSG.ProperTwoGeneratedCore
