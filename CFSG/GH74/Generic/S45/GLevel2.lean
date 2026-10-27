module

public import CFSG.GH74.Generic.S45.GLevel1
public import CFSG.GH74.Generic.S45.OrbitCore
public import CFSG.GH74.Generic.S45.AutCard

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G]

structure Conf2 {x : G} (S₀ R₀ : Subgroup (CentralizerBar x)) (T : Subgroup G) : Prop where
  lift : SylowLift x S₀ T
  R_le : R₀ ≤ S₀
  R_card : Nat.card ↥R₀ = 8
  z_notin : xbar x ∉ R₀
  S_comm : ∀ a ∈ S₀, ∀ b ∈ S₀, a * b = b * a
  S_sq : ∀ a ∈ S₀, a * a = 1
  S_card : Nat.card ↥S₀ = 16
  trans : ∀ r ∈ R₀, r ≠ 1 → ∀ s ∈ R₀, s ≠ 1 →
    ∃ ν ∈ normalizer (S₀ : Set (CentralizerBar x)), ν * r * ν⁻¹ = s
  card_norm : Nat.card ↥(normalizer (S₀ : Set (CentralizerBar x))) =
    21 * Nat.card ↥(centralizer (S₀ : Set (CentralizerBar x)))

section Basic

variable {x : G} {S₀ R₀ : Subgroup (CentralizerBar x)} {T : Subgroup G}

@[expose] def Rg (x : G) (R₀ : Subgroup (CentralizerBar x)) (T : Subgroup G) : Subgroup G :=
  T ⊓ Pre x R₀

theorem mem_Rg {t : G} : t ∈ Rg x R₀ T ↔ t ∈ T ∧ t ∈ centralizer ({x} : Set G) ∧ piC x t ∈ R₀ :=
  ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩⟩

theorem Rg_le : Rg x R₀ T ≤ T := inf_le_left

theorem Conf2.x_not_Rg (h : Conf2 S₀ R₀ T) : x ∉ Rg x R₀ T := by
  intro hx
  have := (mem_Rg.1 hx).2.2
  rw [piC_x] at this
  exact h.z_notin this

theorem piC_conj (x : G) {n t : G} (hn : n ∈ centralizer ({x} : Set G))
    (ht : t ∈ centralizer ({x} : Set G)) :
    piC x (n * t * n⁻¹) = piC x n * piC x t * (piC x n)⁻¹ := by
  rw [piC_mul x (mul_mem hn ht) (inv_mem hn), piC_mul x hn ht, piC_inv x hn]

theorem piC_conj_inv (x : G) {n t : G} (hn : n ∈ centralizer ({x} : Set G))
    (ht : t ∈ centralizer ({x} : Set G)) :
    piC x (n⁻¹ * t * n) = (piC x n)⁻¹ * piC x t * piC x n := by
  rw [piC_mul x (mul_mem (inv_mem hn) ht) hn, piC_mul x (inv_mem hn) ht, piC_inv x hn]

theorem conj_mem_T {n t : G} (hn : n ∈ normalizer (T : Set G)) (ht : t ∈ T) : n * t * n⁻¹ ∈ T :=
  (Subgroup.mem_normalizer_iff.1 hn t).1 ht

theorem conj_inv_mem_T {n t : G} (hn : n ∈ normalizer (T : Set G)) (ht : t ∈ T) :
    n⁻¹ * t * n ∈ T := by
  have := (Subgroup.mem_normalizer_iff.1 (inv_mem hn) t).1 ht
  simpa using this

theorem Conf2.conj_eq (hc : Conf2 S₀ R₀ T) {ν s a : CentralizerBar x}
    (hν : ν ∈ normalizer (S₀ : Set (CentralizerBar x))) (hs : s ∈ S₀) (ha : a ∈ S₀) :
    (s * ν) * a * (s * ν)⁻¹ = ν * a * ν⁻¹ := by
  have hb : ν * a * ν⁻¹ ∈ S₀ := (Subgroup.mem_normalizer_iff.1 hν a).1 ha
  have h1 : s * (ν * a * ν⁻¹) = (ν * a * ν⁻¹) * s := hc.S_comm s hs _ hb
  calc (s * ν) * a * (s * ν)⁻¹ = s * (ν * a * ν⁻¹) * s⁻¹ := by group
    _ = ν * a * ν⁻¹ := by rw [h1]; group

end Basic

section Card

variable [Finite G] {x : G} {S₀ R₀ : Subgroup (CentralizerBar x)} {T : Subgroup G}

theorem SylowLift.card_eq (h : SylowLift x S₀ T) : Nat.card ↥T = Nat.card ↥S₀ := by
  refine Nat.card_congr (Equiv.ofBijective (fun t : ↥T => (⟨piC x t, h.piC_mem t.2⟩ : ↥S₀))
    ⟨?_, ?_⟩)
  · intro a b hab
    exact Subtype.ext (h.piC_inj a.2 b.2 (congrArg Subtype.val hab))
  · rintro ⟨σ, hσ⟩
    obtain ⟨t, ht, rfl⟩ := (h.image σ).1 hσ
    exact ⟨⟨t, ht⟩, rfl⟩

theorem Conf2.card_Rg (h : Conf2 S₀ R₀ T) : Nat.card ↥(Rg x R₀ T) = 8 := by
  rw [← h.R_card]
  refine Nat.card_congr (Equiv.ofBijective
    (fun t : ↥(Rg x R₀ T) => (⟨piC x t, (mem_Rg.1 t.2).2.2⟩ : ↥R₀)) ⟨?_, ?_⟩)
  · intro a b hab
    exact Subtype.ext (h.lift.piC_inj (mem_Rg.1 a.2).1 (mem_Rg.1 b.2).1 (congrArg Subtype.val hab))
  · rintro ⟨σ, hσ⟩
    obtain ⟨t, ht, rfl⟩ := (h.lift.image σ).1 (h.R_le hσ)
    exact ⟨⟨t, mem_Rg.2 ⟨ht, h.lift.le_C ht, hσ⟩⟩, rfl⟩

end Card

section Frattini

variable [Finite G] {x : G} {S₀ : Subgroup (CentralizerBar x)} {T : Subgroup G}

theorem exists_lift_normalizer (h : SylowLift x S₀ T) {ν : CentralizerBar x}
    (hν : ν ∈ normalizer (S₀ : Set (CentralizerBar x))) :
    ∃ n : G, n ∈ normalizer (T : Set G) ∧ n ∈ centralizer ({x} : Set G) ∧
      ∃ s ∈ S₀, piC x n = s * ν := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({x} : Set G) with hC
  set T' : Subgroup ↥C := T.subgroupOf C with hT'
  have hT'S : T'.map (proj x) = S₀ := by
    ext z
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [h.image]
      exact ⟨(u : G), hu, piC_of_mem x u.2⟩
    · intro hz
      obtain ⟨t, ht, rfl⟩ := (h.image z).1 hz
      have htC := h.le_C ht
      exact ⟨⟨t, htC⟩, ht, (piC_of_mem x htC).symm⟩
  have hT'syl : IsSylowOf 2 T' ⊤ := by
    have h1 := (isSylowOf_iff.1 h.sylow)
    rw [isSylowOf_iff]
    refine ⟨le_top, h.sylow.isPGroup.comap_subtype, ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact h1.2.2
  have hn : ∀ s : CentralizerBar x, s ∈ T'.map (proj x) ↔ ν * s * ν⁻¹ ∈ T'.map (proj x) := by
    intro s
    rw [hT'S]
    exact Subgroup.mem_normalizer_iff.1 hν s
  obtain ⟨n, hnN, s, hs, hπn⟩ := frattini_lift (proj x) (QuotientGroup.mk'_surjective _) hT'syl hn
  have hn' := Subgroup.mem_normalizer_iff.1 hnN
  refine ⟨(n : G), ?_, n.2, s, hT'S ▸ hs, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · intro ht
      have htC := h.le_C ht
      have := (hn' ⟨t, htC⟩).1 ht
      exact this
    · intro ht
      have htC : t ∈ C := by
        have h1 : (n : G) * t * (n : G)⁻¹ ∈ C := h.le_C ht
        have : t = (n : G)⁻¹ * ((n : G) * t * (n : G)⁻¹) * (n : G) := by group
        rw [this]
        exact mul_mem (mul_mem (inv_mem n.2) h1) n.2
      exact (hn' ⟨t, htC⟩).2 ht
  · rw [piC_of_mem x n.2]
    exact hπn

end Frattini

section Transport

variable [Finite G] {x : G} {S₀ R₀ : Subgroup (CentralizerBar x)} {T : Subgroup G}

@[expose] def Msub (x : G) (T : Subgroup G) : Subgroup G :=
  normalizer (T : Set G) ⊓ centralizer ({x} : Set G)

omit [Finite G] in
theorem mem_Msub {n : G} :
    n ∈ Msub x T ↔ n ∈ normalizer (T : Set G) ∧ n ∈ centralizer ({x} : Set G) := Iff.rfl

omit [Finite G] in
theorem Msub_le_N (x : G) (T : Subgroup G) : Msub x T ≤ normalizer (T : Set G) := inf_le_left

omit [Finite G] in
theorem Msub_le_C (x : G) (T : Subgroup G) : Msub x T ≤ centralizer ({x} : Set G) := inf_le_right

@[expose] noncomputable def rhoT (x : G) (T : Subgroup G) : ↥(Msub x T) →* MulAut ↥T :=
  T.normalizerMonoidHom.comp (Subgroup.inclusion (Msub_le_N x T))

omit [Finite G] in
theorem rhoT_coe (n : ↥(Msub x T)) (t : ↥T) :
    (((rhoT x T) n t : ↥T) : G) = (n : G) * (t : G) * (n : G)⁻¹ := rfl

@[expose] noncomputable def piM (x : G) (T : Subgroup G) : ↥(Msub x T) →* CentralizerBar x :=
  (proj x).comp (Subgroup.inclusion (Msub_le_C x T))

omit [Finite G] in
theorem piM_eq (n : ↥(Msub x T)) : piM x T n = piC x (n : G) :=
  (piC_of_mem x (Msub_le_C x T n.2)).symm

omit [Finite G] in
theorem piM_mem_normalizer (h : SylowLift x S₀ T) (n : ↥(Msub x T)) :
    piM x T n ∈ normalizer (S₀ : Set (CentralizerBar x)) := by
  have hnN : (n : G) ∈ normalizer (T : Set G) := Msub_le_N x T n.2
  have hnC : (n : G) ∈ centralizer ({x} : Set G) := Msub_le_C x T n.2
  rw [Subgroup.mem_normalizer_iff]
  intro s
  rw [piM_eq]
  constructor
  · intro hs
    obtain ⟨t, ht, rfl⟩ := (h.image s).1 hs
    rw [← piC_conj x hnC (h.le_C ht)]
    exact h.piC_mem (conj_mem_T hnN ht)
  · intro hs
    obtain ⟨t, ht, ht'⟩ := (h.image _).1 hs
    have h1 : (n : G)⁻¹ * t * (n : G) ∈ T := conj_inv_mem_T hnN ht
    have key : piC x ((n : G)⁻¹ * t * (n : G)) = s := by
      rw [piC_conj_inv x hnC (h.le_C ht), ht']
      group
    rw [← key]
    exact h.piC_mem h1

@[expose] noncomputable def phiS (h : SylowLift x S₀ T) :
    ↥(Msub x T) →* ↥(normalizer (S₀ : Set (CentralizerBar x))) :=
  (piM x T).codRestrict _ (piM_mem_normalizer h)

@[expose] noncomputable def rhoS (h : SylowLift x S₀ T) : ↥(Msub x T) →* MulAut ↥S₀ :=
  S₀.normalizerMonoidHom.comp (phiS h)

omit [Finite G] in
theorem rhoS_coe (h : SylowLift x S₀ T) (n : ↥(Msub x T)) (s : ↥S₀) :
    (((rhoS h) n s : ↥S₀) : CentralizerBar x) =
      piC x (n : G) * (s : CentralizerBar x) * (piC x (n : G))⁻¹ := by
  rw [← piM_eq]
  rfl

theorem ker_rho_eq (hc : Conf2 S₀ R₀ T) : (rhoT x T).ker = (rhoS hc.lift).ker := by
  ext n
  have hnN : (n : G) ∈ normalizer (T : Set G) := Msub_le_N x T n.2
  have hnC : (n : G) ∈ centralizer ({x} : Set G) := Msub_le_C x T n.2
  simp only [MonoidHom.mem_ker]
  constructor
  · intro h1
    refine MulEquiv.ext fun s => Subtype.ext ?_
    obtain ⟨t, ht, ht'⟩ := (hc.lift.image s).1 s.2
    have h1' : (rhoT x T n) ⟨t, ht⟩ = ⟨t, ht⟩ := by rw [h1]; rfl
    have hfix : (n : G) * t * (n : G)⁻¹ = t := congrArg Subtype.val h1'
    rw [rhoS_coe, ← ht', ← piC_conj x hnC (hc.lift.le_C ht), hfix]
    exact ht'
  · intro h2
    refine MulEquiv.ext fun t => Subtype.ext ?_
    have hT1 : (n : G) * (t : G) * (n : G)⁻¹ ∈ T := conj_mem_T hnN t.2
    have h2' : (rhoS hc.lift n) ⟨piC x t, hc.lift.piC_mem t.2⟩ = ⟨piC x t, hc.lift.piC_mem t.2⟩ := by
      rw [h2]; rfl
    have h3' : piC x (n : G) * piC x t * (piC x (n : G))⁻¹ = piC x t := by
      have := congrArg Subtype.val h2'
      rw [rhoS_coe] at this
      exact this
    have h3 : piC x ((n : G) * t * (n : G)⁻¹) = piC x t := by
      rw [piC_conj x hnC (hc.lift.le_C t.2)]
      exact h3'
    exact hc.lift.piC_inj hT1 t.2 h3

theorem range_rhoS (hc : Conf2 S₀ R₀ T) :
    (rhoS hc.lift).range = S₀.normalizerMonoidHom.range := by
  ext f
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨phiS hc.lift n, rfl⟩
  · rintro ⟨ν, rfl⟩
    obtain ⟨n, hnN, hnC, s, hs, hπ⟩ := exists_lift_normalizer hc.lift ν.2
    refine ⟨⟨n, mem_Msub.2 ⟨hnN, hnC⟩⟩, ?_⟩
    refine MulEquiv.ext fun a => Subtype.ext ?_
    rw [rhoS_coe]
    show piC x n * (a : CentralizerBar x) * (piC x n)⁻¹ =
      (ν : CentralizerBar x) * (a : CentralizerBar x) * (ν : CentralizerBar x)⁻¹
    rw [hπ]
    exact hc.conj_eq ν.2 hs a.2

theorem card_range_rhoT (hc : Conf2 S₀ R₀ T) : Nat.card ↥(rhoT x T).range = 21 := by
  rw [card_range_eq_of_ker_eq (rhoT x T) (rhoS hc.lift) (ker_rho_eq hc), range_rhoS hc]
  have h2 := card_range_normalizerMonoidHom_mul S₀
  rw [hc.card_norm] at h2
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2

theorem fusion_step (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a) {x : G}
    (hx : orderOf x = 2) {S₀ R₀ : Subgroup (CentralizerBar x)} {T : Subgroup G}
    (hc : Conf2 S₀ R₀ T) (h315 : ∀ A' : Subgroup (MulAut ↥T), Nat.card ↥A' ≠ 315) :
    (∀ n ∈ normalizer (T : Set G), x⁻¹ * (n * x * n⁻¹) ∈ Rg x R₀ T) ∧
    (∀ r ∈ Rg x R₀ T, ∃ n ∈ normalizer (T : Set G), n * x * n⁻¹ = x * r) ∧
    Nat.card ↥T.normalizerMonoidHom.range = 168 ∧
    (∀ t ∈ T, t ∉ Rg x R₀ T → x⁻¹ * t ∈ Rg x R₀ T) := by
  have hxT : x ∈ T := hc.lift.x_mem hx
  have hab : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s := fun s hs t ht => hc.lift.comm hc.S_comm hs ht
  have hcomm' : ∀ a b : ↥T, a * b = b * a := fun a b => Subtype.ext (hab a a.2 b b.2)
  have hsq' : ∀ a : ↥T, a * a = 1 := fun a => Subtype.ext (hc.lift.sq_eq_one hc.S_sq a.2)
  have hcard' : Nat.card ↥T = 16 := hc.lift.card_eq.trans hc.S_card
  have hR' : Nat.card ↥((Rg x R₀ T).subgroupOf T) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Rg_le).toEquiv]
    exact hc.card_Rg
  have hmemR' : ∀ t : ↥T, t ∈ (Rg x R₀ T).subgroupOf T ↔ (t : G) ∈ Rg x R₀ T :=
    fun t => Subgroup.mem_subgroupOf
  have hxR' : (⟨x, hxT⟩ : ↥T) ∉ (Rg x R₀ T).subgroupOf T :=
    fun h => hc.x_not_Rg ((hmemR' _).1 h)
  have hBA : (rhoT x T).range ≤ T.normalizerMonoidHom.range := by
    rintro _ ⟨n, rfl⟩
    exact ⟨_, rfl⟩
  have hBx : ∀ f ∈ (rhoT x T).range, f ⟨x, hxT⟩ = ⟨x, hxT⟩ := by
    rintro _ ⟨n, rfl⟩
    apply Subtype.ext
    show (n : G) * x * (n : G)⁻¹ = x
    have hnC : (n : G) ∈ centralizer ({x} : Set G) := Msub_le_C x T n.2
    have h1 : x * (n : G) = (n : G) * x :=
      Subgroup.mem_centralizer_iff.1 hnC x (Set.mem_singleton x)
    exact mul_inv_eq_iff_eq_mul.2 h1.symm
  have hAB : ∀ f ∈ T.normalizerMonoidHom.range, f ⟨x, hxT⟩ = ⟨x, hxT⟩ →
      f ∈ (rhoT x T).range := by
    rintro _ ⟨⟨n, hnN⟩, rfl⟩ hf
    have hnx : n * x * n⁻¹ = x := congrArg Subtype.val hf
    have hnC : n ∈ centralizer ({x} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (mul_inv_eq_iff_eq_mul.1 hnx).symm
    exact ⟨⟨n, mem_Msub.2 ⟨hnN, hnC⟩⟩, rfl⟩
  have hne : ∀ t : ↥T, t ≠ 1 → piC x (t : G) ≠ 1 := by
    intro t ht h
    apply ht
    apply Subtype.ext
    exact hc.lift.piC_inj t.2 (one_mem T) (h.trans (piC_one x).symm)
  have htrans : ∀ r ∈ (Rg x R₀ T).subgroupOf T, r ≠ 1 → ∀ s ∈ (Rg x R₀ T).subgroupOf T, s ≠ 1 →
      ∃ f ∈ (rhoT x T).range, f r = s := by
    intro r hr hr1 s hs hs1
    have hrR := (hmemR' r).1 hr
    have hsR := (hmemR' s).1 hs
    obtain ⟨ν, hν, hνrs⟩ := hc.trans _ (mem_Rg.1 hrR).2.2 (hne r hr1) _ (mem_Rg.1 hsR).2.2
      (hne s hs1)
    obtain ⟨n, hnN, hnC, s', hs', hπ⟩ := exists_lift_normalizer hc.lift hν
    refine ⟨rhoT x T ⟨n, mem_Msub.2 ⟨hnN, hnC⟩⟩, ⟨_, rfl⟩, ?_⟩
    apply Subtype.ext
    show n * (r : G) * n⁻¹ = (s : G)
    apply hc.lift.piC_inj (conj_mem_T hnN r.2) s.2
    rw [piC_conj x hnC (hc.lift.le_C r.2), hπ, hc.conj_eq hν hs' (hc.lift.piC_mem r.2), hνrs]
  have hnon : ∃ f ∈ T.normalizerMonoidHom.range, f ⟨x, hxT⟩ ≠ ⟨x, hxT⟩ := by
    obtain ⟨g, hg, hne⟩ := exists_nonisolated hs hn hx hc.lift.sylow hxT hab
    obtain ⟨n, hnN, hnx⟩ := exists_mem_normalizer_conj_eq hc.lift.sylow hxT hab hg
    refine ⟨T.normalizerMonoidHom ⟨n, hnN⟩, ⟨_, rfl⟩, fun h => hne ?_⟩
    rw [← hnx]
    exact congrArg Subtype.val h
  obtain ⟨h1, h2⟩ := orbit_analysis hcomm' hsq' hcard' ((Rg x R₀ T).subgroupOf T) hR' hxR'
    T.normalizerMonoidHom.range (rhoT x T).range hBA hBx hAB htrans (card_range_rhoT hc) hnon h315
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn'
    exact (hmemR' _).1 (h1 (T.normalizerMonoidHom ⟨n, hn'⟩) ⟨_, rfl⟩)
  · intro r hr
    obtain ⟨f, hf, hfx⟩ := h2 ⟨r, (mem_Rg.1 hr).1⟩ ((hmemR' _).2 hr)
    obtain ⟨⟨n, hnN⟩, rfl⟩ := hf
    exact ⟨n, hnN, congrArg Subtype.val hfx⟩
  · exact card_A_eq _ hR' _ _ hBA hBx hAB (card_range_rhoT hc) h1 h2
  · intro t ht htR
    rcases mem_or_mem_coset hcomm' hcard' ((Rg x R₀ T).subgroupOf T) hR' hxR' ⟨t, ht⟩ with h | h
    · exact absurd ((hmemR' _).1 h) htR
    · exact (hmemR' _).1 h

end Transport

end CFSG.GH74.Generic.S45
