module

public import CFSG.CGT.PushingUpLit.T2KR.Fus613Basis

public section

namespace CFSG.CGT.PushingUpLit.T2KR.P613

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.T2K CFSG.CGT.Timmesfeld75
open scoped commutatorElement
open MData (QM)

variable {G : Type} [Group G] [Finite G] {L M : Subgroup G} {n : ℕ}

theorem card_SL2_of_card_four {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 4) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = 60 := by
  rw [Matrix.card_SL_field, hF, Fin.prod_univ_two]
  norm_num

section Counts

variable {H : MData G L M n} {T' : Subgroup G} {x r b : G} (c : Cfg H T' x r b)

include c in
theorem Cfg.card_L : Nat.card ↥L = 960 := by
  have hF : Fintype.card (Fq n) = 4 := by rw [H.hcard, c.n_eq]; norm_num
  have h1 := Subgroup.card_ker_mul_card_range H.D.φ
  have hrange : H.D.φ.range = ⊤ := MonoidHom.range_eq_top.2 H.D.φ_surj
  have hker : H.D.φ.ker = (blockU L).subgroupOf L := by
    ext l
    rw [MonoidHom.mem_ker, H.D.φ_ker, c.hO]
    rfl
  have hV : Nat.card (H.D.φ.ker) = 16 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (blockU_le L)).toEquiv]
    exact c.card_V
  rw [hrange, Subgroup.card_top, card_SL2_of_card_four hF, hV] at h1
  omega

include c in
theorem Cfg.blockU_le_N0 : blockU L ≤ T' ⊓ L :=
  le_inf (H.blockU_le_QM.trans c.Q_le) (blockU_le L)

include c in
theorem Cfg.isSylow_N0 : CFSG.ABGLocalTools.IsSylowOf 2 (T' ⊓ L) L :=
  ((c.syl.of_le c.T'_M le_top).inf_of_le_normalizer H.le H.normal)

include c in
theorem Cfg.card_N0 : Nat.card ↥(T' ⊓ L) = 64 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [c.isSylow_N0.card_eq, c.card_L, Nat.factorization_def _ Nat.prime_two]
  decide +kernel

include c in
theorem Cfg.comm_mem_blockU {m : G} (hm : m ∈ T' ⊓ L) : (m * r)⁻¹ * (r * m) ∈ blockU L := by
  classical
  set N0 : Subgroup G := T' ⊓ L with hN0
  let V' : Subgroup ↥N0 := (blockU L).subgroupOf N0
  have hV'n : V'.Normal := ⟨fun v hv g => by
    have hv' : (v : G) ∈ blockU L := hv
    show (g : G) * (v : G) * (g : G)⁻¹ ∈ blockU L
    exact conj_mem_blockU (H.normal (H.le g.2.2)) hv'⟩
  have hcardV' : Nat.card V' = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe c.blockU_le_N0).toEquiv]
    exact c.card_V
  have hidx : V'.index = 4 := by
    have := Subgroup.card_mul_index V'
    rw [hcardV', c.card_N0] at this
    omega
  have hq : Nat.card (↥N0 ⧸ V') = 2 ^ 2 := by
    show V'.index = 2 ^ 2
    rw [hidx]
    norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm := IsPGroup.isMulCommutative_of_card_eq_prime_sq hq
  have hrN : r ∈ N0 := ⟨c.r_T, c.r_L⟩
  have e := hcomm.is_comm.comm (QuotientGroup.mk (⟨m, hm⟩ : ↥N0) : ↥N0 ⧸ V')
    (QuotientGroup.mk ⟨r, hrN⟩)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at e
  simpa [V', Subgroup.mem_subgroupOf] using e

theorem _root_.CFSG.CGT.PushingUpLit.T2KR.MData.act_blockU {v : G} (H : MData G L M n)
    (hv : v ∈ blockU L) (w : Fin 2 → Fq n) : H.act v w = w := by
  have h1 := H.conj_vec (H.le (blockU_le L hv)) w
  have h2 : v * H.vec w = H.vec w * v := H.nat.blockU_comm v hv _ (H.vec_mem w)
  have h3 : v * H.vec w * v⁻¹ = H.vec w := by rw [h2]; group
  rw [h3] at h1
  exact (H.vec_injective h1).symm

include c in
theorem Cfg.act_comm_r {m : G} (hm : m ∈ T' ⊓ L) (w : Fin 2 → Fq n) :
    H.act m (H.act r w) = H.act r (H.act m w) := by
  have hMm : m ∈ M := H.le hm.2
  have hrM : r ∈ M := H.le c.r_L
  have hy : H.act ((m * r)⁻¹ * (r * m)) w = w := MData.act_blockU H (c.comm_mem_blockU hm) w
  have hy' : H.act (m * r)⁻¹ (H.act (r * m) w) = w := by
    rw [← H.act_mul (M.mul_mem hrM hMm) w]
    exact hy
  have := congrArg (H.act (m * r)) hy'
  rw [H.act_act_inv (M.mul_mem hMm hrM)] at this
  rw [← H.act_mul hrM w, ← H.act_mul hMm w]
  exact this.symm

section Tv

variable {e₁ e₂ : Fin 2 → Fq n} {ω : Fq n}

theorem IsTv.unique {a : G} {s s' : Fq n} (he₁ : e₁ ≠ 0) (h : IsTv H e₁ e₂ a s)
    (h' : IsTv H e₁ e₂ a s') : s = s' := by
  have : (s - s') • e₁ = 0 := by
    rw [sub_smul]
    have := h.shift.symm.trans h'.shift
    have h2 : s • e₁ = s' • e₁ := add_left_cancel this
    rw [h2, sub_self]
  exact sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_right he₁)

theorem IsTv.mul {a a' : G} {s s' : Fq n} (h : IsTv H e₁ e₂ a s) (h' : IsTv H e₁ e₂ a' s')
    (ha : a ∈ L) (ha'M : a' ∈ M) : IsTv H e₁ e₂ (a * a') (s + s') := by
  refine ⟨?_, ?_⟩
  · rw [H.act_mul ha'M, h'.fix, h.fix]
  · rw [H.act_mul ha'M, h'.shift, H.act_add (H.le ha), H.act_smul_L ha, h.fix, h.shift]
    module

include c in
theorem Cfg.isTv_of_mem_N0 (bs : Basis H r b e₁ e₂ ω) {m : G} (hm : m ∈ T' ⊓ L) :
    ∃ s, IsTv H e₁ e₂ m s := by
  have hmL : m ∈ L := hm.2
  have hmM : m ∈ M := H.le hmL
  have hcomm := c.act_comm_r hm
  obtain ⟨p, q, hpq⟩ := bs.span (H.act m e₂)
  have htv_r : IsTv H e₁ e₂ r 1 := ⟨bs.r1, by rw [one_smul]; exact bs.r2⟩
  have h1 : H.act m e₁ = q • e₁ := by
    have e1 := hcomm e₂
    rw [bs.r2, H.act_add hmM, hpq, htv_r.act_coord c.r_L] at e1
    linear_combination (norm := module) e1
  have hT2 : IsPGroup 2 T' := c.syl.isPGroup
  obtain ⟨k, hk⟩ := hT2 ⟨m, hm.1⟩
  have hmk : m ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hpow : ∀ j : ℕ, H.act (m ^ j) e₁ = q ^ j • e₁ := by
    intro j
    induction j with
    | zero => simp [H.act_one]
    | succ j ih =>
      rw [pow_succ, H.act_mul hmM, h1, H.act_smul_L (Subgroup.pow_mem L hmL j), ih, smul_smul,
        pow_succ, mul_comm]
  have hq1 : q = 1 := by
    have := hpow (2 ^ k)
    rw [hmk, H.act_one] at this
    have h2 : (q ^ 2 ^ k - 1) • e₁ = 0 := by
      rw [sub_smul, ← this, one_smul, sub_self]
    have h3 : q ^ 2 ^ k = 1 := sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right bs.e₁_ne)
    exact eq_one_of_pow_two_pow_eq_one h3
  subst hq1
  refine ⟨p, ?_, ?_⟩
  · rw [h1, one_smul]
  · rw [hpq]
    module

theorem IsTv.one (e₁ e₂ : Fin 2 → Fq n) : IsTv H e₁ e₂ (1 : G) 0 :=
  ⟨H.act_one e₁, by rw [H.act_one, zero_smul, add_zero]⟩

noncomputable def Cfg.tvParam (c : Cfg H T' x r b) (bs : Basis H r b e₁ e₂ ω)
    (m : ↥(T' ⊓ L)) : Fq n :=
  Classical.choose (c.isTv_of_mem_N0 bs m.2)

theorem Cfg.tvParam_spec (c : Cfg H T' x r b) (bs : Basis H r b e₁ e₂ ω) (m : ↥(T' ⊓ L)) :
    IsTv H e₁ e₂ (m : G) (c.tvParam bs m) :=
  Classical.choose_spec (c.isTv_of_mem_N0 bs m.2)

@[expose] noncomputable def Cfg.par (c : Cfg H T' x r b) (bs : Basis H r b e₁ e₂ ω) :
    ↥(T' ⊓ L) →* Multiplicative (Fq n) where
  toFun m := Multiplicative.ofAdd (c.tvParam bs m)
  map_one' := by
    have h := IsTv.unique bs.e₁_ne (c.tvParam_spec bs 1) (IsTv.one (H := H) e₁ e₂)
    show Multiplicative.ofAdd (c.tvParam bs 1) = 1
    rw [h]
    rfl
  map_mul' m m' := by
    have h1 : IsTv H e₁ e₂ ((m * m' : ↥(T' ⊓ L)) : G) (c.tvParam bs m + c.tvParam bs m') :=
      (c.tvParam_spec bs m).mul (c.tvParam_spec bs m') m.2.2 (H.le m'.2.2)
    have h := IsTv.unique bs.e₁_ne (c.tvParam_spec bs (m * m')) h1
    show Multiplicative.ofAdd (c.tvParam bs (m * m')) =
      Multiplicative.ofAdd (c.tvParam bs m) * Multiplicative.ofAdd (c.tvParam bs m')
    rw [h]
    rfl

theorem Cfg.par_apply (c : Cfg H T' x r b) (bs : Basis H r b e₁ e₂ ω) (m : ↥(T' ⊓ L)) :
    c.par bs m = Multiplicative.ofAdd (c.tvParam bs m) := rfl

include c in
theorem Cfg.ker_par (bs : Basis H r b e₁ e₂ ω) :
    (c.par bs).ker = (blockU L).subgroupOf (T' ⊓ L) := by
  ext m
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, c.par_apply]
  constructor
  · intro h
    have h0 : c.tvParam bs m = 0 := by
      have := congrArg Multiplicative.toAdd h
      simpa using this
    have hs := c.tvParam_spec bs m
    rw [h0] at hs
    have hmM : (m : G) ∈ M := H.le m.2.2
    have hact : ∀ w, H.act m w = w := by
      intro w
      obtain ⟨α, β, rfl⟩ := bs.span w
      rw [H.act_add hmM, H.act_smul_L m.2.2, H.act_smul_L m.2.2, hs.fix, hs.shift]
      module
    rw [← c.hO]
    refine NatData.mem_oTwoIn_of_centralizes H.D m.2.2 fun v hv => ?_
    have h1 := H.conj_vec hmM (H.D.ψe v)
    rw [H.vec_ψe hv, hact] at h1
    rw [h1, H.vec_ψe hv]
  · intro h
    have hs : IsTv H e₁ e₂ (m : G) 0 :=
      ⟨MData.act_blockU H h e₁, by rw [MData.act_blockU H h e₂, zero_smul, add_zero]⟩
    have := IsTv.unique bs.e₁_ne (c.tvParam_spec bs m) hs
    rw [this]
    rfl

include c in
theorem Cfg.exists_mem_N0_isTv (bs : Basis H r b e₁ e₂ ω) (s : Fq n) :
    ∃ m ∈ T' ⊓ L, IsTv H e₁ e₂ m s := by
  have hF : Nat.card (Fq n) = 4 := by
    rw [Nat.card_eq_fintype_card, H.hcard, c.n_eq]; norm_num
  have h1 := Subgroup.card_ker_mul_card_range (c.par bs)
  have hker : Nat.card (c.par bs).ker = 16 := by
    rw [c.ker_par bs,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe c.blockU_le_N0).toEquiv]
    exact c.card_V
  rw [hker, c.card_N0] at h1
  have hrange : Nat.card (c.par bs).range = 4 := by omega
  have htop : (c.par bs).range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hrange, Nat.card_congr Multiplicative.toAdd, hF]
  have : Multiplicative.ofAdd s ∈ (c.par bs).range := by rw [htop]; exact Subgroup.mem_top _
  obtain ⟨m, hm⟩ := this
  refine ⟨m, m.2, ?_⟩
  have := c.tvParam_spec bs m
  have h2 : c.tvParam bs m = s := by
    have := congrArg Multiplicative.toAdd hm
    simpa [c.par_apply] using this
  rwa [h2] at this

end Tv

end Counts

end CFSG.CGT.PushingUpLit.T2KR.P613
