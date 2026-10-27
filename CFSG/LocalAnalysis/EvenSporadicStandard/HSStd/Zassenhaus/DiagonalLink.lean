module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.MaximalLinks

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open scoped commutatorElement
open Subgroup Relation CFSG.Blueprint CFSG.Blueprint.NativeSporadic
  CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78

variable {G : Type} [Group G]

theorem center_quotient_center_eq_bot {L : Type} [Group L] (hL : CFSG.IsQuasisimple L) :
    center (L ⧸ center L) = ⊥ := by
  obtain ⟨-, hsimple, a, b, hab⟩ := hL
  have := hsimple
  have hn : (center (L ⧸ center L)).Normal := inferInstance
  rcases hn.eq_bot_or_eq_top with h | h
  · exact h
  · exact absurd ((mem_center_iff.1 (h ▸ mem_top b)) a) hab

theorem nonempty_quotient_center_equiv_range {L : Type} [Group L] (hL : CFSG.IsQuasisimple L)
    (φ : L →* G) (hker : φ.ker ≤ center L) :
    Nonempty (L ⧸ center L ≃* ↥φ.range ⧸ center ↥φ.range) := by
  have hZ := center_quotient_center_eq_bot hL
  let ψ : L →* ↥φ.range ⧸ center ↥φ.range := (QuotientGroup.mk' _).comp φ.rangeRestrict
  have hψ : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective _).comp φ.rangeRestrict_surjective
  have hk : ψ.ker = center L := by
    ext a
    simp only [MonoidHom.mem_ker, ψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    constructor
    · intro ha
      have hφ : ∀ b : L, φ a * φ b = φ b * φ a := by
        intro b
        have := congrArg Subtype.val ((mem_center_iff.1 ha) (φ.rangeRestrict b))
        simp only [Subgroup.coe_mul, MonoidHom.coe_rangeRestrict] at this
        exact this.symm
      have hcomm : ∀ b : L, b⁻¹ * a⁻¹ * b * a ∈ center L := by
        intro b
        apply hker
        rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
        calc (φ b)⁻¹ * (φ a)⁻¹ * φ b * φ a = (φ b)⁻¹ * (φ a)⁻¹ * (φ b * φ a) := by group
          _ = (φ b)⁻¹ * (φ a)⁻¹ * (φ a * φ b) := by rw [hφ b]
          _ = 1 := by group
      have hcen : (QuotientGroup.mk a : L ⧸ center L) ∈ center (L ⧸ center L) := by
        rw [mem_center_iff]
        intro y
        induction y using QuotientGroup.induction_on with
        | H b =>
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
          rw [show (b * a)⁻¹ * (a * b) = (b⁻¹ * a⁻¹ * b * a)⁻¹ by group]
          exact (center L).inv_mem (hcomm b)
      rw [hZ, mem_bot, QuotientGroup.eq_one_iff] at hcen
      exact hcen
    · intro ha
      rw [mem_center_iff]
      intro y
      obtain ⟨b, rfl⟩ := φ.rangeRestrict_surjective y
      apply Subtype.ext
      simp only [Subgroup.coe_mul, MonoidHom.coe_rangeRestrict]
      rw [← map_mul, ← map_mul, (mem_center_iff.1 ha) b]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)⟩

theorem commutatorElement_mul_central_of_mem {Q : Type*} [Group Q] {z w : Q}
    (hz : z ∈ center Q) (hw : w ∈ center Q) (x y : Q) : ⁅z * x, w * y⁆ = ⁅x, y⁆ := by
  have hz' := mem_center_iff.mp hz
  have hw' := mem_center_iff.mp hw
  rw [commutatorElement_def, commutatorElement_def]
  calc z * x * (w * y) * (z * x)⁻¹ * (w * y)⁻¹
      = z * (x * w * y * x⁻¹) * z⁻¹ * y⁻¹ * w⁻¹ := by group
    _ = (x * w * y * x⁻¹) * z * z⁻¹ * y⁻¹ * w⁻¹ := by rw [← hz' (x * w * y * x⁻¹)]
    _ = (w * x * y * x⁻¹ * y⁻¹) * w⁻¹ := by rw [hw' x]; group
    _ = w * (x * y * x⁻¹ * y⁻¹) * w⁻¹ := by group
    _ = (x * y * x⁻¹ * y⁻¹) * w * w⁻¹ := by rw [← hw' (x * y * x⁻¹ * y⁻¹)]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem eq_top_of_isSubnormal_of_perfect {Q : Type*} [Group Q] (hQ : CFSG.IsQuasisimple Q)
    {N : Subgroup Q} (hN : N.IsSubnormal) (hNp : Group.IsPerfect N) (hN1 : N ≠ ⊥) : N = ⊤ := by
  obtain ⟨hperf, hsimple, -⟩ := hQ
  have h1 : (N.map (QuotientGroup.mk' (center Q))).IsSubnormal :=
    hN.map (QuotientGroup.mk'_surjective _)
  rcases h1.eq_bot_or_top_of_isSimpleGroup hsimple with hbot | htop
  · exfalso
    have hle : N ≤ center Q := by
      rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    apply hN1
    have hcomm : ⁅N, N⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro n hn m hm
      exact (mem_center_iff.mp (hle hn) m)
    rw [← Subgroup.isPerfect_iff.mp hNp, hcomm]
  · have hsup : N ⊔ center Q = ⊤ := by
      have h2 := Subgroup.comap_map_eq (QuotientGroup.mk' (center Q)) N
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at h2
      exact h2.symm
    have hle : commutator Q ≤ N := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro x _ y _
      have hx : x ∈ N ⊔ center Q := hsup ▸ mem_top x
      have hy : y ∈ N ⊔ center Q := hsup ▸ mem_top y
      obtain ⟨n, hn, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
      obtain ⟨n', hn', z', hz', rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
      have e : ⁅n * z, n' * z'⁆ = ⁅n, n'⁆ := by
        rw [mem_center_iff.mp hz n, mem_center_iff.mp hz' n']
        exact commutatorElement_mul_central_of_mem hz hz' n n'
      rw [e, commutatorElement_def]
      exact N.mul_mem (N.mul_mem (N.mul_mem hn hn') (N.inv_mem hn)) (N.inv_mem hn')
    rw [hperf.commutator_eq_top] at hle
    exact top_le_iff.mp hle

theorem isSubnormal_subgroupOf_of_le {K R X : Subgroup G} (hRX : R ≤ X)
    (h : (K.subgroupOf X).IsSubnormal) : (K.subgroupOf R).IsSubnormal := by
  have h1 := h.subgroupOf (K := R.subgroupOf X)
  let e : ↥(R.subgroupOf X) ≃* ↥R := Subgroup.subgroupOfEquivOfLe hRX
  have h2 := h1.map (f := e.toMonoidHom) e.surjective
  convert h2 using 1
  ext ⟨x, hx⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · intro hxK
    refine ⟨⟨⟨x, hRX hx⟩, hx⟩, ?_, ?_⟩
    · simpa [Subgroup.mem_subgroupOf] using hxK
    · rfl
  · rintro ⟨⟨⟨y, hyX⟩, hyR⟩, hy, hyx⟩
    have : y = x := congrArg Subtype.val hyx
    subst this
    simpa [Subgroup.mem_subgroupOf] using hy


theorem isQuasisimple_range_of_ker_le_center {L : Type} [Group L] (hL : CFSG.IsQuasisimple L)
    (φ : L →* G) (hker : φ.ker ≤ center L) : CFSG.IsQuasisimple ↥φ.range := by
  obtain ⟨e⟩ := nonempty_quotient_center_equiv_range hL φ hker
  obtain ⟨hperf, hsimple, a, b, hab⟩ := hL
  have := hperf
  refine ⟨Group.IsPerfect.ofSurjective φ.rangeRestrict_surjective, ?_, e a, e b, ?_⟩
  · have := hsimple
    have : Nontrivial (↥φ.range ⧸ center ↥φ.range) := e.symm.toEquiv.nontrivial
    exact IsSimpleGroup.isSimpleGroup_of_surjective e.toMonoidHom e.surjective
  · intro h
    apply hab
    have := congrArg e.symm h
    simpa using this

theorem nonempty_quotient_center_equiv_of_ltF_ne [Finite G] {K L : Subgroup G} {s t : G}
    (hs : orderOf s = 2) (hst : s * t = t * s) (hK : IsCompIn K (centralizer ({s} : Set G)))
    (hL : IsCompIn L (centralizer ({t} : Set G)))
    (hKL : K ≤ L ⊔ L.map (MulAut.conj s).toMonoidHom)
    (hne : L.map (MulAut.conj s).toMonoidHom ≠ L) :
    Nonempty (↥L ⧸ center ↥L ≃* ↥K ⧸ center ↥K) := by
  have hc := commute_conj_of_ne hst hL hne
  have hss : s * s = 1 := mul_self_eq_one_of_orderOf_eq_two hs
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  set φ := foldHom s L hc with hφ
  have hker : φ.ker ≤ center ↥L := by
    intro a ha
    rw [MonoidHom.mem_ker, foldHom_apply] at ha
    have hinv : s * (a : G) * s⁻¹ = (a : G)⁻¹ := eq_inv_of_mul_eq_one_right ha
    have hmem : (a : G)⁻¹ ∈ L.map (MulAut.conj s).toMonoidHom :=
      ⟨a, a.2, by simp [MulAut.conj_apply, hinv]⟩
    rw [mem_center_iff]
    intro x
    apply Subtype.ext
    have h1 := hc x x.2 _ hmem
    simp only [Subgroup.coe_mul]
    calc (x : G) * a = (a : G) * ((a : G)⁻¹ * x) * a := by group
      _ = (a : G) * (x * (a : G)⁻¹) * a := by rw [h1]
      _ = a * x := by group
  have hR := isQuasisimple_range_of_ker_le_center hL.isQuasisimple φ hker
  have hRs : φ.range ≤ centralizer ({s} : Set G) := by
    rintro _ ⟨a, rfl⟩
    rw [mem_centralizer_singleton_iff, foldHom_apply]
    have h1 := hc a a.2 (s * a * s⁻¹) ⟨a, a.2, by simp [MulAut.conj_apply]⟩
    calc (a : G) * (s * a * s⁻¹) * s = s * (s⁻¹ * (a * (s * a * s⁻¹)) * s) := by group
      _ = s * ((s⁻¹ * a * s) * a) := by group
      _ = s * ((s * a * s⁻¹) * a) := by rw [hsi]
      _ = s * (a * (s * a * s⁻¹)) := by rw [h1]
  have hKR : K ≤ φ.range :=
    le_range_foldHom hss hc (fun _ hx => hK.le hx) hK.isQuasisimple.1 hKL
  have hsub : (K.subgroupOf φ.range).IsSubnormal := isSubnormal_subgroupOf_of_le hRs hK.2.2
  have hKq := hK.isQuasisimple
  have htop : K.subgroupOf φ.range = ⊤ := by
    refine eq_top_of_isSubnormal_of_perfect hR hsub ?_ ?_
    · have := hKq.1
      exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKR).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hKR).symm.surjective
    · intro hbot
      obtain ⟨-, -, a, b, hab⟩ := hKq
      have hK1 : Subsingleton ↥K := by
        refine ⟨fun x y => ?_⟩
        have hx : (⟨x, hKR x.2⟩ : ↥φ.range) ∈ K.subgroupOf φ.range := x.2
        have hy : (⟨y, hKR y.2⟩ : ↥φ.range) ∈ K.subgroupOf φ.range := y.2
        rw [hbot, mem_bot] at hx hy
        apply Subtype.ext
        have hx' := congrArg Subtype.val hx
        have hy' := congrArg Subtype.val hy
        simp only [OneMemClass.coe_one] at hx' hy'
        rw [hx', hy']
      have h1 : ∀ q : ↥K ⧸ center ↥K, q = 1 := by
        intro q
        induction q using QuotientGroup.induction_on with
        | H x => rw [Subsingleton.elim x 1]; rfl
      exact hab (by rw [h1 a, h1 b])
  have hKeq : K = φ.range := by
    apply le_antisymm hKR
    intro x hx
    have : (⟨x, hx⟩ : ↥φ.range) ∈ K.subgroupOf φ.range := htop ▸ mem_top _
    exact this
  obtain ⟨e⟩ := nonempty_quotient_center_equiv_range hL.isQuasisimple φ hker
  subst hKeq
  exact ⟨e⟩

theorem maximalF_of_aLinks [Finite G] (h13 : FS79Thm13UseSec G)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) {N : Subgroup G}
    (hN : FStarSimple N) (hperf : ∀ P : Subgroup G, ⁅P, P⁆ = P → P ≤ N) {M : Subgroup G}
    (hM : InLF M) (hMq : IsSporadic (↥M ⧸ center ↥M) .HS)
    (ha : ∀ K L : Subgroup G, ∀ s t : G, orderOf s = 2 → orderOf t = 2 → s * t = t * s →
      IsCompIn K (centralizer ({s} : Set G)) → IsCompIn L (centralizer ({t} : Set G)) →
      L.map (MulAut.conj s).toMonoidHom = L → K ≤ L → IsSporadic (↥K ⧸ center ↥K) .HS → K = L)
    (hrk : ∀ K : Subgroup G, IsSporadic (↥K ⧸ center ↥K) .HS → CFSG.pRank 2 ↥K ≠ 1) :
    MaximalF M := by
  refine maximalF_of_links h13 hkp hN hperf hM hMq ?_ hrk
  intro K L s t hs ht hst hK hL hKL hq
  by_cases hLe : L.map (MulAut.conj s).toMonoidHom = L
  · exact Or.inl (ha K L s t hs ht hst hK hL hLe (le_of_conj_eq hLe hKL) hq)
  · obtain ⟨e⟩ := nonempty_quotient_center_equiv_of_ltF_ne hs hst hK hL hKL hLe
    obtain ⟨f⟩ := hq
    exact Or.inr ⟨hLe, ⟨e.trans f⟩⟩

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
