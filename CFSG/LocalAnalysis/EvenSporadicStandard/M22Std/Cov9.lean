module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.Cov4
public import Certificates.Certificate24821

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.QuasithinUnique.Ch1 CFSG.QuasithinUnique.Ch1.M22Cover CFSG.QuasithinUnique.Ch1.TitsCover
open CFSG.Monster.B.Co2 (rep_compA rep_idA eqA_iff eq_of_eqA)

structure TwFacts (L : Type) [Group L] (t : L) where
  φ : L →* Equiv.Perm (Fin 22)
  S0 : Subgroup (Equiv.Perm (Fin 22))
  z : Equiv.Perm (Fin 22)
  Al : Finset (Equiv.Perm (Fin 22))
  Bl : Finset (Equiv.Perm (Fin 22))
  w₁ : L
  w₂ : L
  ker_iff : ∀ x, φ x = 1 ↔ x = 1 ∨ x = t
  surj : ∀ g ∈ S0, ∃ x, φ x = g
  card_range : Nat.card φ.range = 443520
  card_S0 : Nat.card S0 = 128
  z_mem : z ∈ S0
  z_sq : z * z = 1
  z_ne : z ≠ 1
  z_central : ∀ g ∈ S0, z * g = g * z
  center : ∀ g ∈ S0, (∀ h ∈ S0, g * h = h * g) → g = 1 ∨ g = z
  gen : Subgroup.closure {p : L | φ p ∈ S0 ∧ p * p = 1} = S0.comap φ
  φ_sq : φ (w₁ * w₁) = z
  w₁_mem : φ w₁ ∈ S0
  w₂_mem : φ w₂ ∈ S0
  w_rel : w₁ * w₁ = w₂ * w₂ * t
  Al_card : Al.card = 12
  Bl_card : Bl.card = 8
  Al_sub : ∀ g ∈ Al, g ∈ S0
  roots : ∀ g ∈ S0, g * g = z → g ∈ Al ∨ g ∈ Bl
  Al_sq : ∀ g ∈ Al, ∀ p : L, φ p = g → p * p = w₁ * w₁
  conj : ∀ u : L, u * u = 1 → φ u ≠ 1 →
    ∃ c : L, u = c * (w₁ * w₁) * c⁻¹ ∨ u = c * (w₂ * w₂) * c⁻¹
  not_sq : ∀ g : L, g * g ≠ t

theorem aV_lt : ∀ v ∈ aV, v < 128 := by decide

theorem rootsV_lt : ∀ v ∈ rootsV, v < 128 := by decide

theorem IsM22Cover.nonempty_twFacts
    {L : Type} [Group L] [Finite L] [Group.IsPerfect L] {t : L}
    (h : IsM22Cover L t) : Nonempty (TwFacts L t) := by
  classical
  obtain ⟨e⟩ := h.quotient
  let X := h.centralExt e
  have hrange := h.centralExt_range e
  have hφmem := h.centralExt_mem e
  have hT := covCheck_good covCheck_covData
  have hx : ∀ i, CFSG.Monster.B.Co2.Rep 22 (covData.xa i) (covData.x i) :=
    fun i => covData.xa_rep i
  have hxmem : ∀ i, covData.x i ∈ NativeSporadic.M22 := fun i => wordP_mem _
  choose xt hxt using fun i : Fin 3 => hrange (covData.x i) (hxmem i)
  have hck := Certificates.certificate24821
  simp only [twCheck, Bool.and_eq_true] at hck
  obtain ⟨⟨⟨⟨hinv, hcen⟩, hroots⟩, hwalks⟩, hzc⟩ := hck
  obtain ⟨h79, hzsq, hzne, hzcomm⟩ := twZ_sound hx hzc
  have hnV : covData.nV = 128 := covData_nV
  let S0 : Subgroup (Equiv.Perm (Fin 22)) := covData.tab.sub covData.x hT
  have hS0 : ∀ g, g ∈ S0 ↔ ∃ v < covData.nV, covData.tab.el covData.x v = g := fun g => Iff.rfl
  have elmem : ∀ v < covData.nV, covData.tab.el covData.x v ∈ S0 := fun v hv => ⟨v, hv, rfl⟩
  have S0le : ∀ g ∈ S0, g ∈ NativeSporadic.M22 := by
    rintro g ⟨v, -, rfl⟩
    exact Subgroup.list_prod_mem _ fun y hy => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
      exact hxmem i
  have el0 : covData.tab.el covData.x 0 = 1 := by simp [CayTab.el, hT.word_zero]
  have xmemS0 : ∀ i, covData.x i ∈ S0 := fun i => by
    have h1 := hT.el_tgt 0 hT.zero_lt i
    rw [el0, one_mul] at h1
    exact ⟨covData.tab.tgt 0 i, hT.tgt_lt 0 hT.zero_lt i, h1⟩
  have hzS0 : covData.tab.el covData.x 79 * covData.tab.el covData.x 79 ∈ S0 :=
    S0.mul_mem (elmem 79 h79) (elmem 79 h79)
  have hphisig : ∀ v, X.φ (sig covData.tab xt v) = covData.tab.el covData.x v :=
    fun v => phi_sig X xt hxt covData.tab v
  have hker : ∀ x : L, X.φ x = 1 ↔ x = 1 ∨ x = t := fun x => ⟨X.ker x, fun hx' => by
    rcases hx' with rfl | rfl
    · exact map_one _
    · exact X.φ_ζ⟩
  have hAl : ∀ v ∈ aV, ∀ p : L, X.φ p = covData.tab.el covData.x v →
      p * p = sig covData.tab xt 79 * sig covData.tab xt 79 := by
    intro v hv p hp
    simp only [twWalks, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hwalks
    obtain ⟨⟨hvlt, hclosed⟩, hred⟩ := hwalks v hv
    have hlift : ∀ bl ∈ covData.blocks, ∃ gt : L, X.φ gt = bl.g := fun bl _ =>
      hrange _ bl.g_mem
    have hsum := walk_sum_eq_zero covData covCheck_covData X xt hxt hlift hred
    have hpsi := closed_walk X xt hT hxt hT.zero_lt hclosed
    rw [hsum, X.toZ_zero] at hpsi
    have h1 : psi xt (sqWalk covData v 79) = sig covData.tab xt v * sig covData.tab xt v *
        (sig covData.tab xt 79)⁻¹ * (sig covData.tab xt 79)⁻¹ := by
      simp only [sqWalk, psi_append, psi_posW, psi_invW]
      rfl
    rw [h1] at hpsi
    have hsq : sig covData.tab xt v * sig covData.tab xt v =
        sig covData.tab xt 79 * sig covData.tab xt 79 := by
      calc sig covData.tab xt v * sig covData.tab xt v
          = (sig covData.tab xt v * sig covData.tab xt v * (sig covData.tab xt 79)⁻¹ *
            (sig covData.tab xt 79)⁻¹) * (sig covData.tab xt 79 * sig covData.tab xt 79) := by
            group
        _ = sig covData.tab xt 79 * sig covData.tab xt 79 := by rw [hpsi, one_mul]
    have hpk : X.φ (p * (sig covData.tab xt v)⁻¹) = 1 := by
      rw [map_mul, map_inv, hp, hphisig v, mul_inv_cancel]
    rcases X.ker _ hpk with h1 | h1
    · have : p = sig covData.tab xt v := by
        have h2 : p * (sig covData.tab xt v)⁻¹ = 1 := h1
        have := congrArg (· * sig covData.tab xt v) h2
        simpa using this
      rw [this]
      exact hsq
    · have : p = t * sig covData.tab xt v := by
        have h2 : p * (sig covData.tab xt v)⁻¹ = t := h1
        have := congrArg (· * sig covData.tab xt v) h2
        simpa using this
      rw [this]
      calc t * sig covData.tab xt v * (t * sig covData.tab xt v)
          = (t * t) * (sig covData.tab xt v * sig covData.tab xt v) := by
            rw [mul_assoc, ← mul_assoc (sig covData.tab xt v), ← h.t_central (sig covData.tab xt v),
              mul_assoc t, mul_assoc]
        _ = sig covData.tab xt 79 * sig covData.tab xt 79 := by rw [h.mul_self_t, one_mul, hsq]
  let Al : Finset (Equiv.Perm (Fin 22)) := (aV.map (covData.tab.el covData.x)).toFinset
  let Bl : Finset (Equiv.Perm (Fin 22)) :=
    ((rootsV.filter fun v => decide (v ∉ aV)).map (covData.tab.el covData.x)).toFinset
  have hlt : ∀ u, u < 128 → u < covData.tab.nV := fun u hu => by
    show u < covData.nV
    rw [hnV]
    exact hu
  have hinj : ∀ u v, u < 128 → v < 128 →
      covData.tab.el covData.x u = covData.tab.el covData.x v → u = v := fun u v hu hv huv =>
    hT.el_inj u (hlt u hu) v (hlt v hv) huv
  have hAlcard : Al.card = 12 := by
    have hnd : (aV.map (covData.tab.el covData.x)).Nodup :=
      List.Nodup.map_on (fun u hu v hv huv => hinj u v (aV_lt u hu) (aV_lt v hv) huv)
        (by decide)
    rw [List.toFinset_card_of_nodup hnd, List.length_map]
    rfl
  have hBlcard : Bl.card = 8 := by
    have hnd : ((rootsV.filter fun v => decide (v ∉ aV)).map (covData.tab.el covData.x)).Nodup :=
      List.Nodup.map_on (fun u hu v hv huv => hinj u v
        (rootsV_lt u (List.mem_of_mem_filter hu)) (rootsV_lt v (List.mem_of_mem_filter hv)) huv)
        (by decide)
    rw [List.toFinset_card_of_nodup hnd, List.length_map]
    rfl
  have hrangeφ : X.φ.range = NativeSporadic.M22 := by
    ext y
    constructor
    · rintro ⟨e', rfl⟩
      exact hφmem e'
    · intro hy
      exact hrange y hy
  have hgen : Subgroup.closure {p : L | X.φ p ∈ S0 ∧ p * p = 1} = S0.comap X.φ := by
    set V := Subgroup.closure {p : L | X.φ p ∈ S0 ∧ p * p = 1} with hV
    have hVle : V ≤ S0.comap X.φ := (Subgroup.closure_le (S0.comap X.φ)).2 fun p hp => hp.1
    have hlift : ∀ i, ∃ p ∈ V, X.φ p = covData.x i := by
      intro i
      obtain ⟨p, hp⟩ := hrange (covData.x i) (hxmem i)
      by_cases h1 : covData.x i = 1
      · exact ⟨1, V.one_mem, by rw [map_one, h1]⟩
      · have hord : orderOf ((p : L) : L ⧸ center L) = 2 := by
          have hinj' : Function.Injective (toPerm.comp e.toMonoidHom) :=
            toPerm_injective.comp e.injective
          rw [← orderOf_injective _ hinj']
          have : (toPerm.comp e.toMonoidHom) (p : L ⧸ center L) = X.φ p := rfl
          rw [this, hp]
          exact orderOf_eq_prime (by rw [sq]; exact twInv_sound hx hinv i) h1
        have hpp : p * p = 1 := h.mul_self_of_lift hord
        exact ⟨p, Subgroup.subset_closure ⟨by rw [hp]; exact xmemS0 i, hpp⟩, hp⟩
    choose xt' hxt'V hxt' using hlift
    have hsigV : ∀ v, sig covData.tab xt' v ∈ V := fun v =>
      Subgroup.list_prod_mem V fun y hy => by
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
        exact hxt'V i
    have htV : t ∈ V := by
      by_contra htV
      have hnV63 : 189 / 3 < covData.tab.nV := by
        show 189 / 3 < covData.nV
        rw [hnV]
        norm_num
      have hkap : kap covData.tab xt' (189 / 3) (fo 189) = 1 := by
        have hmemV : kap covData.tab xt' (189 / 3) (fo 189) ∈ V := by
          unfold kap
          exact V.mul_mem (V.inv_mem (hsigV _)) (V.mul_mem (hsigV _) (hxt'V _))
        have hphi : X.φ (kap covData.tab xt' (189 / 3) (fo 189)) = 1 :=
          phi_kap X xt' hT hxt' hnV63 (fo 189)
        rcases X.ker _ hphi with h1 | h1
        · exact h1
        · have hζV : X.ζ ∈ V := h1 ▸ hmemV
          exact absurd hζV htV
      refine false_of_double_cover X hrange hφmem xt' hxt' (fun e' he' => ?_)
      rw [covData_free] at he'
      have : e' = 189 := by simpa using he'
      subst this
      unfold cE
      simp only [hkap, ↓reduceIte]
    refine le_antisymm hVle fun p hp => ?_
    obtain ⟨v, hv, hel⟩ := (hS0 _).1 hp
    have hq : X.φ (sig covData.tab xt' v) = X.φ p := by
      rw [phi_sig X xt' hxt' covData.tab v, hel]
    have hpk : X.φ (p * (sig covData.tab xt' v)⁻¹) = 1 := by
      rw [map_mul, map_inv, ← hq, mul_inv_cancel]
    rcases X.ker _ hpk with h1 | h1
    · have : p = sig covData.tab xt' v := by
        have h2 : p * (sig covData.tab xt' v)⁻¹ = 1 := h1
        have := congrArg (· * sig covData.tab xt' v) h2
        simpa using this
      rw [this]
      exact hsigV v
    · have : p = t * sig covData.tab xt' v := by
        have h2 : p * (sig covData.tab xt' v)⁻¹ = t := h1
        have := congrArg (· * sig covData.tab xt' v) h2
        simpa using this
      rw [this]
      exact V.mul_mem htV (hsigV v)
  refine ⟨{
    φ := X.φ
    S0 := S0
    z := covData.tab.el covData.x 79 * covData.tab.el covData.x 79
    Al := Al
    Bl := Bl
    w₁ := sig covData.tab xt 79
    w₂ := sig covData.tab xt 7
    ker_iff := hker
    surj := fun g hg => hrange g (S0le g hg)
    card_range := ?_
    card_S0 := (CayTab.card_sub hT).trans hnV
    z_mem := hzS0
    z_sq := hzsq
    z_ne := hzne
    z_central := ?_
    center := ?_
    gen := hgen
    φ_sq := ?_
    w₁_mem := ?_
    w₂_mem := ?_
    w_rel := h.sig_sq_rel e xt hxt
    Al_card := hAlcard
    Bl_card := hBlcard
    Al_sub := ?_
    roots := ?_
    Al_sq := ?_
    conj := ?_
    not_sq := h.not_sq_t }⟩
  · rw [hrangeφ]
    exact CFSG.Sporadic.Mathieu.card_M22
  · rintro g ⟨v, hv, rfl⟩
    exact hzcomm v hv
  · rintro g ⟨v, hv, rfl⟩ hcomm
    exact twCenter_sound hx h79 hcen v hv fun i => hcomm _ (xmemS0 i)
  · show X.φ _ = _
    rw [map_mul, hphisig 79]
  · show X.φ _ ∈ S0
    rw [hphisig 79]
    exact elmem 79 h79
  · show X.φ _ ∈ S0
    rw [hphisig 7]
    exact elmem 7 (by rw [hnV]; norm_num)
  · intro g hg
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hg)
    exact elmem v (by rw [hnV]; exact aV_lt v hv)
  · rintro g ⟨v, hv, rfl⟩ hgg
    have hvr := (twRoots_sound hx h79 hroots v hv).1 hgg
    by_cases hva : v ∈ aV
    · left
      exact List.mem_toFinset.2 (List.mem_map.2 ⟨v, hva, rfl⟩)
    · right
      exact List.mem_toFinset.2 (List.mem_map.2 ⟨v, List.mem_filter.2 ⟨hvr, by simpa using hva⟩,
        rfl⟩)
  · intro g hg p hp
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hg)
    exact hAl v hv p hp
  · intro u hu2 hu1
    have hmk : (u : L ⧸ center L) ≠ 1 := fun hmk => hu1 (by
      show toPerm (e (u : L ⧸ center L)) = 1
      rw [hmk, map_one, map_one])
    have hord : orderOf (u : L ⧸ center L) = 2 :=
      orderOf_eq_prime (by rw [sq, ← QuotientGroup.mk_mul, hu2, QuotientGroup.mk_one]) hmk
    obtain ⟨cb, hc⟩ := h.involution_conj (h.orderOf_sig_sq e xt hxt) hord
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective cb
    have hyc : (u : L ⧸ center L) =
        ((c * (sig covData.tab xt 79 * sig covData.tab xt 79) * c⁻¹ : L) : L ⧸ center L) := by
      rw [hc]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    refine ⟨c, ?_⟩
    rcases h.eq_or_eq_mul_t_of_mk_eq hyc with h1 | h1
    · exact Or.inl h1
    · right
      have h3 : sig covData.tab xt 7 * sig covData.tab xt 7 =
          sig covData.tab xt 79 * sig covData.tab xt 79 * t := by
        rw [h.sig_sq_rel e xt hxt, mul_assoc, h.mul_self_t, mul_one]
      rw [h1, h3]
      calc c * (sig covData.tab xt 79 * sig covData.tab xt 79) * c⁻¹ * t
          = c * (sig covData.tab xt 79 * sig covData.tab xt 79) * (c⁻¹ * t) := by
            simp only [mul_assoc]
        _ = c * (sig covData.tab xt 79 * sig covData.tab xt 79) * (t * c⁻¹) := by
            rw [h.t_central c⁻¹]
        _ = c * (sig covData.tab xt 79 * sig covData.tab xt 79 * t) * c⁻¹ := by
            simp only [mul_assoc]

end CFSG.EvenSporadicStandard.M22Std
