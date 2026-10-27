module

public import CFSG.Certificates.Kernel.Fin76bAut.Pi
import CFSG.Certificates.Kernel.Spor.PK.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13EDef
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13HAut

public section

universe u

namespace CFSG.KS.EAut

open CFSG.KC.Enum CFSG.KS CFSG.KS.PK CFSG.KS.Prim CFSG.KS.PEnum
  CFSG.EvenSporadicStandard.Fin76b CFSG.EvenSporadicStandard.Fin76b.AutETable
  CFSG.EvenSporadicStandard.Fin76b.E69

theorem eG_zero_of_lt {a : ℕ} (ha : a < 64) : eG a 0 = a := by
  rw [eG_eq]
  simp [Nat.mod_eq_of_lt ha]

theorem eKlGen_fields {A B e : ℕ} (he : e < 64) (ha : eG A e < 64) (hb : eG B e < 64)
    (hab : eG A (eG B e) < 64) :
    eG (eKlGen A B e) 0 = e ∧ eG (eKlGen A B e) 1 = eG A e ∧ eG (eKlGen A B e) 2 = eG B e ∧
      eG (eKlGen A B e) 3 = eG A (eG B e) := by
  have e1 : eKlGen A B e = Nat.lor (Nat.lor (Nat.lor e (Nat.shiftLeft (eG A e) (Nat.mul 6 1)))
      (Nat.shiftLeft (eG B e) (Nat.mul 6 2))) (Nat.shiftLeft (eG A (eG B e)) (Nat.mul 6 3)) := by
    unfold eKlGen
    change e ||| (eG A e <<< 6 ||| (eG B e <<< 12 ||| eG A (eG B e) <<< 18)) =
      ((e ||| eG A e <<< 6) ||| eG B e <<< 12) ||| eG A (eG B e) <<< 18
    rw [Nat.or_assoc, Nat.or_assoc]
  have h1 : e < 2 ^ (6 * 1) := by norm_num; omega
  have h2 : Nat.lor e (Nat.shiftLeft (eG A e) (Nat.mul 6 1)) < 2 ^ (6 * 2) := pack_lt h1 ha
  have h3 : Nat.lor (Nat.lor e (Nat.shiftLeft (eG A e) (Nat.mul 6 1)))
      (Nat.shiftLeft (eG B e) (Nat.mul 6 2)) < 2 ^ (6 * 3) := pack_lt h2 hb
  rw [e1]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [eG_pack h3 hab (by norm_num), if_pos (by norm_num), eG_pack h2 hb (by norm_num),
      if_pos (by norm_num), eG_pack h1 ha (by norm_num), if_pos (by norm_num), eG_zero_of_lt he]
  · rw [eG_pack h3 hab (by norm_num), if_pos (by norm_num), eG_pack h2 hb (by norm_num),
      if_pos (by norm_num), eG_pack h1 ha (by norm_num), if_neg (by norm_num)]
  · rw [eG_pack h3 hab (by norm_num), if_pos (by norm_num), eG_pack h2 hb (by norm_num),
      if_neg (by norm_num)]
  · rw [eG_pack h3 hab (by norm_num), if_neg (by norm_num)]

@[expose] def kX {Γ : Type*} [Group Γ] (α β : Γ) (b : ℕ) : Γ :=
  if b = 0 then 1 else if b = 1 then α else if b = 2 then β else α * β

theorem kX_inj {Γ : Type*} [Group Γ] {α β : Γ} (h1 : α ≠ 1) (h2 : β ≠ 1) (h3 : α ≠ β)
    (h4 : α * β ≠ 1) (h5 : α * β ≠ α) (h6 : α * β ≠ β) :
    ∀ b < 4, ∀ b' < 4, kX α β b = kX α β b' → b = b' := by
  intro b hb b' hb' h
  interval_cases b <;> interval_cases b' <;> first
    | rfl
    | (exfalso
       first
        | exact h1 h | exact h1 h.symm | exact h2 h | exact h2 h.symm | exact h3 h
        | exact h3 h.symm | exact h4 h | exact h4 h.symm | exact h5 h | exact h5 h.symm
        | exact h6 h | exact h6 h.symm)

theorem kX_mem {Γ : Type*} [Group Γ] (α β : Γ) (b : ℕ) :
    kX α β b ∈ Subgroup.closure ({α, β} : Set Γ) := by
  unfold kX
  split_ifs
  · exact one_mem _
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)
  · exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))

theorem eClsK_rep {cnt nr nv : ℕ} {T REP IV ICL ICJ : ℕ → ℕ}
    (h : eClsK cnt T nr REP nv IV ICL ICJ = true) : ∀ r < nr, REP r < cnt := by
  intro r hr
  unfold eClsK at h
  rw [bAnd_eq, Bool.and_eq_true] at h
  have h2 := allN_iff.1 h.1 r hr
  rw [strictB_eq, bAnd_eq, Bool.and_eq_true] at h2
  exact Nat.le_of_ble_eq_true h2.1

section Group

variable {H : Type u} [Group H]

theorem inn_conj {χ ψ : MulAut H} (h : ψ ∈ (MulAut.conj : H →* MulAut H).range) :
    χ * ψ * χ⁻¹ ∈ (MulAut.conj : H →* MulAut H).range :=
  Subgroup.Normal.conj_mem inferInstance ψ h χ

@[expose] def IsB (π : MulAut H →* Equiv.Perm (Fin 5)) (φ : MulAut H) : Prop :=
  φ * φ = 1 ∧ π φ ∈ alternatingGroup (Fin 5) ∧ φ ∉ (MulAut.conj : H →* MulAut H).range

theorem isB_conj {π : MulAut H →* Equiv.Perm (Fin 5)} {χ ρ φ : MulAut H} (h : χ * ρ = φ * χ)
    (hb : IsB π φ) : IsB π ρ := by
  have hρ : ρ = χ⁻¹ * φ * χ := by rw [mul_assoc, ← h, ← mul_assoc, inv_mul_cancel, one_mul]
  subst hρ
  obtain ⟨h1, h2, h3⟩ := hb
  refine ⟨?_, ?_, fun hm => h3 ?_⟩
  · calc χ⁻¹ * φ * χ * (χ⁻¹ * φ * χ) = χ⁻¹ * (φ * φ) * χ := by group
      _ = 1 := by rw [h1, mul_one, inv_mul_cancel]
  · have := Subgroup.Normal.conj_mem inferInstance (π φ) h2 (π χ)⁻¹
    rwa [inv_inv, ← map_inv, ← map_mul, ← map_mul] at this
  · have e : χ * (χ⁻¹ * φ * χ) * χ⁻¹ = φ := by group
    rw [← e]
    exact inn_conj hm

@[expose] def KleinF (α β : MulAut H) : Prop :=
  (∀ e : H, α e = e → β e = e) ∧
  (∃ e₀ : H, Subgroup.closure ({e₀, α e₀, β e₀, α (β e₀)} : Set H) = ⊤) ∧
  Nat.card ↥((MulAut.conj : H →* MulAut H).range ⊔ Subgroup.closure ({α, β} : Set (MulAut H))) =
    64 ∧
  ∀ ψ ∈ (MulAut.conj : H →* MulAut H).range ⊔ Subgroup.closure ({α, β} : Set (MulAut H)),
    ψ * ψ = 1 → 16 ≤ Nat.card ↥(((MulAut.conj : H →* MulAut H).range ⊔
      Subgroup.closure ({α, β} : Set (MulAut H))) ⊓ Subgroup.centralizer ({ψ} : Set (MulAut H)))

theorem klein_conj [Finite (MulAut H)] (χ : MulAut H) {α β : MulAut H} (h : KleinF α β) :
    KleinF (χ * α * χ⁻¹) (χ * β * χ⁻¹) := by
  obtain ⟨h1, ⟨e₀, h2⟩, h3, h4⟩ := h
  let γ : MulAut H →* MulAut H := (MulAut.conj χ).toMonoidHom
  have hγ : ∀ ψ, γ ψ = χ * ψ * χ⁻¹ := fun ψ => rfl
  have hγinj : Function.Injective γ := (MulAut.conj χ).injective
  have hinn : ((MulAut.conj : H →* MulAut H).range).map γ = (MulAut.conj : H →* MulAut H).range := by
    ext ψ
    constructor
    · rintro ⟨n, hn, rfl⟩
      rw [hγ]
      exact inn_conj hn
    · intro hψ
      refine ⟨χ⁻¹ * ψ * χ⁻¹⁻¹, inn_conj hψ, ?_⟩
      rw [hγ]
      group
  have hSg : (MulAut.conj : H →* MulAut H).range ⊔
      Subgroup.closure ({χ * α * χ⁻¹, χ * β * χ⁻¹} : Set (MulAut H)) =
      ((MulAut.conj : H →* MulAut H).range ⊔ Subgroup.closure ({α, β} : Set (MulAut H))).map γ := by
    rw [Subgroup.map_sup, hinn, MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
      hγ, hγ]
  refine ⟨fun e he => ?_, ⟨χ e₀, ?_⟩, ?_, fun ψ hψ hψ2 => ?_⟩
  · simp only [MulAut.mul_apply] at he ⊢
    have he' : α (χ⁻¹ e) = χ⁻¹ e := by
      have := congrArg (fun x => (χ⁻¹ : MulAut H) x) he
      simpa only [MulAut.inv_apply_self] using this
    rw [h1 _ he', MulAut.apply_inv_self]
  · have himg : ({χ e₀, (χ * α * χ⁻¹) (χ e₀), (χ * β * χ⁻¹) (χ e₀),
        (χ * α * χ⁻¹) ((χ * β * χ⁻¹) (χ e₀))} : Set H) =
        (χ : MulAut H).toMonoidHom '' {e₀, α e₀, β e₀, α (β e₀)} := by
      simp [Set.image_insert_eq, MulAut.mul_apply]
    rw [himg, ← MonoidHom.map_closure, h2]
    exact Subgroup.map_top_of_surjective _ (MulEquiv.surjective χ)
  · rw [hSg, Subgroup.card_map_of_injective hγinj, h3]
  · rw [hSg] at hψ ⊢
    obtain ⟨ψ₀, hψ₀, rfl⟩ := hψ
    have hψ₀2 : ψ₀ * ψ₀ = 1 := hγinj (by rw [map_mul, hψ2, map_one])
    refine le_trans (h4 ψ₀ hψ₀ hψ₀2) (Nat.card_le_card_of_injective
      (fun y => ⟨γ y.1, Subgroup.mem_inf.2 ⟨?_, ?_⟩⟩)
      fun y z e => Subtype.ext (hγinj (congrArg Subtype.val e)))
    · exact ⟨y.1, (Subgroup.mem_inf.1 y.2).1, rfl⟩
    · rw [Subgroup.mem_centralizer_iff]
      rintro _ rfl
      have hc := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 y.2).2 ψ₀ rfl
      rw [← map_mul, ← map_mul, hc]

end Group

section Lab

variable {H : Type u} [Group H] {M : Array (Array ℕ)} {elt : ℕ → H} (R : Realizes H 32 M elt)
  {ET : ℕ → ℕ} (hM : ∀ a < 32, ∀ b < 32, mt M a b = eMul ET a b)

include R hM

theorem top_of_gen {S k f : ℕ} (hS : ∀ j < k, eG S j < 32) (hgen : eGenK ET S k f = true)
    {K : Subgroup H} (hK : ∀ j < k, elt (eG S j) ∈ K) : K = ⊤ := by
  let Good : ℕ → Prop := fun X => ∀ b, X.testBit b = true → b < 32 ∧ elt b ∈ K
  have hstep : ∀ X, Good X → Good (eGenStep ET S k X) := by
    intro X hX
    unfold eGenStep
    refine foldUp_inv hX fun a ha s hs => ?_
    rw [nIf_eq]
    split_ifs with hb
    · rw [hasBit_eq] at hb
      obtain ⟨-, hab⟩ := hX a hb
      refine foldUp_inv hs fun j hj s' hs' b hbit => ?_
      have hlor : Nat.lor s' (Nat.shiftLeft (nat_lit 1) (eMul ET a (eG S j))) =
          s' ||| 2 ^ eMul ET a (eG S j) := by
        rw [← one_mul (2 ^ eMul ET a (eG S j)), ← Nat.shiftLeft_eq]
        rfl
      rw [hlor, Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow] at hbit
      rcases hbit with hbit | hbit
      · exact hs' b hbit
      · have hbm : eMul ET a (eG S j) = b := of_decide_eq_true hbit
        subst hbm
        refine ⟨tmul_lt R hM ha (hS j hj), ?_⟩
        rw [← hM a ha _ (hS j hj), R.mul _ _ ha (hS j hj)]
        exact mul_mem hab (hK j hj)
    · exact hs
  have hreach : ∀ f, Good (eGenReach ET S k f) := by
    intro f
    induction f with
    | zero =>
      intro b hb
      change (2 ^ 0 : ℕ).testBit b = true at hb
      rw [Nat.testBit_two_pow] at hb
      have hb0 : b = 0 := (of_decide_eq_true hb).symm
      subst hb0
      exact ⟨by norm_num, by rw [R.one]; exact K.one_mem⟩
    | succ f ih =>
      change Good (strictN (eGenReach ET S k f) (fun X => eGenStep ET S k X))
      rw [strictN_eq]
      exact hstep _ ih
  have hfull : eGenReach ET S k f = 2 ^ 32 - 1 := beq_t.1 hgen
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨a, ha, rfl⟩ := R.surj x
  refine (hreach f a ?_).2
  rw [hfull, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true ha

theorem fix_of_eFixK {ρ : MulAut H} {p : ℕ} (hρ : Acts R ρ p) (h : eFixK ET p = true) :
    Nat.card {e : H // ρ e = e} = 4 ∧ ∀ e : H, ρ e = e → e * e = 1 := by
  classical
  unfold eFixK at h
  rw [bAnd_eq, Bool.and_eq_true, beq_t, allN_iff] at h
  obtain ⟨hcnt, hsq⟩ := h
  have hfix : ∀ k < 32, ρ (elt k) = elt k ↔ eG p k = k := fun k hk => by
    rw [hρ.elt_eq hk]
    exact ⟨R.inj _ _ (hρ.lt hk) hk, fun e => by rw [e]⟩
  refine ⟨?_, fun e he => ?_⟩
  · have hset : {e : H | ρ e = e} =
        elt '' ↑((Finset.range 32).filter fun x => Nat.beq (eG p x) x = true) := by
      ext e
      constructor
      · intro he
        obtain ⟨k, hk, rfl⟩ := R.surj e
        refine ⟨k, ?_, rfl⟩
        rw [Finset.coe_filter]
        exact ⟨Finset.mem_range.2 hk, beq_t.2 ((hfix k hk).1 he)⟩
      · rintro ⟨k, hk, rfl⟩
        rw [Finset.coe_filter] at hk
        exact (hfix k (Finset.mem_range.1 hk.1)).2 (beq_t.1 hk.2)
    have e1 : Nat.card {e : H // ρ e = e} = Set.ncard {e : H | ρ e = e} := Nat.card_coe_set_eq _
    have h4 := eCnt_eq_card 32 (fun x => Nat.beq (eG p x) x)
    rw [hcnt] at h4
    rw [e1, hset, Set.InjOn.ncard_image fun a ha b hb e => R.inj a b
      (Finset.mem_range.1 (Finset.mem_filter.1 (Finset.mem_coe.1 ha)).1)
      (Finset.mem_range.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hb)).1) e,
      Set.ncard_coe_finset, ← h4]
  · obtain ⟨k, hk, rfl⟩ := R.surj e
    have h1 := hsq k hk
    rw [bIf_eq, if_pos (beq_t.2 ((hfix k hk).1 he))] at h1
    rw [← R.mul _ _ hk hk, hM k hk k hk, beq_t.1 h1, R.one]

theorem coc_of_eCocK {ρ : MulAut H} {p : ℕ} (hρ : Acts R ρ p) (h : eCocK ET p = true) :
    ∀ e : H, e * ρ e = 1 → ∃ c : H, e * ρ c = c := by
  intro e he
  obtain ⟨k, hk, rfl⟩ := R.surj e
  have h1 := allN_iff.1 h k hk
  have hpk := hρ.lt hk
  have h0 : eMul ET k (eG p k) = 0 := by
    apply R.inj _ _ (tmul_lt R hM hk hpk) R.pos
    rw [← hM k hk _ hpk, R.mul _ _ hk hpk, ← hρ.elt_eq hk, he, R.one]
  rw [bIf_eq, if_pos (beq_t.2 h0), eAnyN_iff] at h1
  obtain ⟨c, hc, hcc⟩ := h1
  refine ⟨elt c, ?_⟩
  rw [hρ.elt_eq hc, ← R.mul _ _ hk (hρ.lt hc), hM k hk _ (hρ.lt hc), beq_t.1 hcc]

end Lab

section Rec

variable {H : Type u} [Group H] {M : Array (Array ℕ)} {elt : ℕ → H} (R : Realizes H 32 M elt)
  {ET T : ℕ → ℕ} {cnt : ℕ} (hM : ∀ a < 32, ∀ b < 32, mt M a b = eMul ET a b)
  {Φ : ℕ → MulAut H} (pd : PosData R T cnt Φ) (hcan : ∀ i < cnt, canonK 32 6 63 192 (T i) = true)
  {nr nv : ℕ} {REP IV ICL ICJ : ℕ → ℕ} (hcls : eClsK cnt T nr REP nv IV ICL ICJ = true)

include pd hcan hcls

theorem inv_pos {φ : MulAut H} (h1 : φ * φ = 1) (h2 : φ ≠ 1) :
    ∃ q < nv, Φ (IV q) = φ ∧ ICL q < nr ∧
      Φ (ICJ q) * Φ (REP (ICL q)) = φ * Φ (ICJ q) := by
  obtain ⟨i, hi, rfl⟩ := pd.surj φ
  have hinvi := ((pd.acts i hi).eInvK_iff (hcan i hi)).2 ⟨h1, h2⟩
  obtain ⟨hinv, hq⟩ := eClsK_spec hcls
  obtain ⟨q, hqv, e⟩ := all_of_sorted hinv (fun q hq' => ⟨(hq q hq').1, (hq q hq').2.2.2.1,
    (hq q hq').2.2.2.2.1⟩) i hi hinvi
  obtain ⟨hv, hl, hcj, -, -, hconj⟩ := hq q hqv
  have hrep := eClsK_rep hcls _ hl
  refine ⟨q, hqv, by rw [e], hl, ?_⟩
  rw [← e]
  exact ((pd.acts _ hcj).mul (pd.acts _ hrep)).ext ((pd.acts _ hv).mul (pd.acts _ hcj))
    fun a _ => by rw [hconj]

end Rec

theorem inn_inj' {ET T INN INE : ℕ → ℕ} {cnt : ℕ} (hinn : eInnK ET cnt T 16 INN INE = true) :
    ∀ u < 16, ∀ u' < 16, INN u = INN u' → u = u' := by
  have hs := eInnK_spec hinn
  have hmono : ∀ i j, i < j → j < 16 → INN i < INN j := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h' | h'
      · exact lt_trans (ih h' (by omega)) ((hs j (by omega)).2.2.1 hj)
      · subst h'
        exact (hs i (by omega)).2.2.1 hj
  intro i hi j hj e
  rcases Nat.lt_trichotomy i j with h' | h' | h'
  · exact absurd e (Nat.ne_of_lt (hmono i j h' hj))
  · exact h'
  · exact absurd e.symm (Nat.ne_of_lt (hmono j i h' hi))

section Main

variable {H : Type u} [Group H] {M : Array (Array ℕ)} {elt : ℕ → H} (R : Realizes H 32 M elt)
  {ET T : ℕ → ℕ} {cnt : ℕ} (hM : ∀ a < 32, ∀ b < 32, mt M a b = eMul ET a b)
  {Φ : ℕ → MulAut H} (pd : PosData R T cnt Φ) (hcan : ∀ i < cnt, canonK 32 6 63 192 (T i) = true)
  {GN kg f c : ℕ} (htup : eTupK ET GN kg f c = true)
  {PR : ℕ} (hpr : ePrK ET PR = true) {π : MulAut H →* Equiv.Perm (Fin 5)}
  (hπ : ∀ (φ : MulAut H) (i j : Fin 5), π φ i = j ↔ (φ (elt (eG PR i)) = elt (eG PR j) ∨
      φ (elt (eG PR i)) = elt (eG PR j) * elt 21))
  {INN INE : ℕ → ℕ} (hker : eKerK ET PR cnt T 16 INN = true)
  (hinn : eInnK ET cnt T 16 INN INE = true)
  {nr nv : ℕ} {REP IV ICL ICJ : ℕ → ℕ} (hcls : eClsK cnt T nr REP nv IV ICL ICJ = true)

include R hM pd hcan htup hpr hπ hker hinn hcls

theorem eBInv_of_isB {φ : MulAut H} {i : ℕ} (hi : i < cnt) (hφ : Φ i = φ) (hb : IsB π φ) :
    eBInv ET PR (T i) = true := by
  subst hφ
  refine eBInv_of R hM hpr hπ (pd.acts i hi) (hcan i hi) hb.1 hb.2.1 fun e => hb.2.2 ?_
  exact (pi_ker R hM (tup_ctr htup) hpr pd hπ hker hinn _).1 e

theorem fix_coc_of_checks (hfix : e613FixK ET PR T nr REP = true) {φ : MulAut H} (hb : IsB π φ) :
    (Nat.card {e : H // φ e = e} = 4 ∧ ∀ e : H, φ e = e → e * e = 1) ∧
      (∀ e : H, e * φ e = 1 → ∃ c : H, e * φ c = c) := by
  have h1 : φ ≠ 1 := fun e => hb.2.2 (e ▸ one_mem _)
  obtain ⟨q, -, -, hl, hconj⟩ := inv_pos R pd hcan hcls hb.1 h1
  have hrep := eClsK_rep hcls _ hl
  obtain ⟨χ, hχ⟩ : ∃ χ, χ = Φ (ICJ q) := ⟨_, rfl⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = Φ (REP (ICL q)) := ⟨_, rfl⟩
  rw [← hχ, ← hρ] at hconj
  have hbρ := isB_conj hconj hb
  have hB := eBInv_of_isB R hM pd hcan htup hpr hπ hker hinn hcls hrep hρ.symm hbρ
  have hfc := allN_iff.1 hfix (ICL q) hl
  rw [strictB_eq, bIf_eq, if_pos hB, bAnd_eq, Bool.and_eq_true] at hfc
  have hA : Acts R ρ (T (REP (ICL q))) := hρ ▸ pd.acts _ hrep
  obtain ⟨hf4, hfsq⟩ := fix_of_eFixK R hM hA hfc.1
  have hcoc := coc_of_eCocK R hM hA hfc.2
  have hφx : ∀ x, φ x = χ (ρ (χ⁻¹ x)) := fun x => by
    have := congrArg (fun ψ : MulAut H => ψ (χ⁻¹ x)) hconj
    simp only [MulAut.mul_apply, MulAut.apply_inv_self] at this
    exact this.symm
  have hfixe : ∀ e, φ e = e ↔ ρ (χ⁻¹ e) = χ⁻¹ e := fun e => by
    rw [hφx]
    constructor
    · intro he
      have := congrArg (fun x => (χ⁻¹ : MulAut H) x) he
      simpa only [MulAut.inv_apply_self] using this
    · intro he
      rw [he, MulAut.apply_inv_self]
  refine ⟨⟨?_, fun e he => ?_⟩, fun e he => ?_⟩
  · rw [← hf4]
    exact Nat.card_congr
      { toFun := fun e => ⟨χ⁻¹ e.1, (hfixe e.1).1 e.2⟩
        invFun := fun e => ⟨χ e.1, (hfixe _).2 (by rw [MulAut.inv_apply_self]; exact e.2)⟩
        left_inv := fun e => Subtype.ext (by simp)
        right_inv := fun e => Subtype.ext (by simp) }
  · have h2 := hfsq _ ((hfixe e).1 he)
    have h3 := congrArg χ h2
    rwa [map_mul, MulAut.apply_inv_self, map_one] at h3
  · have he' : χ⁻¹ e * ρ (χ⁻¹ e) = 1 := by
      have := congrArg (fun x => (χ⁻¹ : MulAut H) x) he
      simp only [map_mul, map_one, hφx, MulAut.inv_apply_self] at this
      exact this
    obtain ⟨c', hc'⟩ := hcoc _ he'
    refine ⟨χ c', ?_⟩
    rw [hφx, MulAut.inv_apply_self]
    have := congrArg χ hc'
    rwa [map_mul, MulAut.apply_inv_self] at this

theorem klein_of_check {α β : MulAut H} {A B : ℕ} (hA : Acts R α A) (hB : Acts R β B)
    (hα : IsB π α) (hβ : IsB π β) (hc : α * β = β * α) (hne : α ≠ β)
    (hnn : α * β ∉ (MulAut.conj : H →* MulAut H).range)
    (hk : eKleinK ET GN kg f T INN A B = true) : KleinF α β := by
  classical
  have := finite_mulAut R
  obtain ⟨hS, hgen⟩ := tup_gen htup
  unfold eKleinK at hk
  rw [strictB_eq] at hk
  simp only [bAnd_eq, Bool.and_eq_true] at hk
  obtain ⟨hfix, hge, hcnt⟩ := hk
  have hAB := hA.mul hB
  have hinnΦ : ∀ u < 16, Φ (INN u) ∈ (MulAut.conj : H →* MulAut H).range := fun u hu =>
    (inn_iff R hM pd (tup_ctr htup) hinn _).2 ⟨u, hu, rfl⟩
  have hα1 : α ≠ 1 := fun e => hα.2.2 (e ▸ one_mem _)
  have hβ1 : β ≠ 1 := fun e => hβ.2.2 (e ▸ one_mem _)
  have hXact : ∀ b < 4, Acts R (kX α β b) (eKlX A B (eC A B) b) := by
    intro b hb
    interval_cases b
    · exact acts_one R
    · exact hA
    · exact hB
    · exact hAB
  let σ : ℕ → MulAut H := fun s => Φ (INN (s / 4)) * kX α β (s % 4)
  have hσact : ∀ s < 64, ∀ y < 32, sg R (σ s) y = eKlAt T INN A B (eC A B) s y := by
    intro s hs y hy
    have hsh : Nat.shiftRight s 2 = s / 4 := by
      change s >>> 2 = s / 4
      rw [Nat.shiftRight_eq_div_pow]
    have hla : Nat.land s 3 = s % 4 := by
      have h := Nat.and_two_pow_sub_one_eq_mod s 2
      norm_num at h
      change s &&& 3 = s % 4
      rw [h]
    unfold eKlAt
    rw [hsh, hla, sg_mul, hXact _ (Nat.mod_lt _ (by norm_num)) y hy,
      pd.acts _ (eInnK_spec hinn _ (by omega)).1 _ ((hXact _ (Nat.mod_lt _ (by norm_num))).lt hy)]
  have hσlt : ∀ s < 64, ∀ y < 32, eKlAt T INN A B (eC A B) s y < 32 := fun s hs y hy =>
    hσact s hs y hy ▸ sg_lt R _ _
  unfold KleinF
  set Sg : Subgroup (MulAut H) := (MulAut.conj : H →* MulAut H).range ⊔
    Subgroup.closure ({α, β} : Set (MulAut H)) with hSgdef
  have hσmem : ∀ s < 64, σ s ∈ Sg := fun s hs => mul_mem
    (Subgroup.mem_sup_left (hinnΦ _ (by omega))) (Subgroup.mem_sup_right (kX_mem α β _))
  have hσsurj : ∀ ψ ∈ Sg, ∃ s < 64, σ s = ψ := by
    intro ψ hψ
    have hψ' : ψ ∈ (((MulAut.conj : H →* MulAut H).range ⊔
        Subgroup.closure ({α, β} : Set (MulAut H)) : Subgroup (MulAut H)) : Set (MulAut H)) := hψ
    rw [Subgroup.normal_mul] at hψ'
    obtain ⟨n, hn, v, hv, rfl⟩ := Set.mem_mul.1 hψ'
    obtain ⟨u, hu, rfl⟩ := (inn_iff R hM pd (tup_ctr htup) hinn _).1 hn
    have hb : ∃ b < 4, kX α β b = v := by
      rcases E613.closure_pair_subset hα.1 hβ.1 hc hv with rfl | rfl | rfl | rfl
      exacts [⟨0, by norm_num, rfl⟩, ⟨1, by norm_num, rfl⟩, ⟨2, by norm_num, rfl⟩,
        ⟨3, by norm_num, rfl⟩]
    obtain ⟨b, hb4, rfl⟩ := hb
    refine ⟨4 * u + b, by omega, ?_⟩
    have e1 : (4 * u + b) / 4 = u := by omega
    have e2 : (4 * u + b) % 4 = b := by omega
    simp only [σ, e1, e2]
  have hab1 : α * β ≠ 1 := fun e => hnn (e ▸ one_mem _)
  have hab2 : α * β ≠ α := fun e => hβ1 (by
    calc β = α⁻¹ * (α * β) := by group
      _ = 1 := by rw [e, inv_mul_cancel])
  have hab3 : α * β ≠ β := fun e => hα1 (by
    calc α = α * β * β⁻¹ := by group
      _ = 1 := by rw [e, mul_inv_cancel])
  have hXinj := kX_inj hα1 hβ1 hne hab1 hab2 hab3
  have hσinj : ∀ s < 64, ∀ s' < 64, σ s = σ s' → s = s' := by
    intro s hs s' hs' e
    have hu : s / 4 < 16 := by omega
    have hu' : s' / 4 < 16 := by omega
    have hb : s % 4 < 4 := Nat.mod_lt _ (by norm_num)
    have hb' : s' % 4 < 4 := Nat.mod_lt _ (by norm_num)
    have e2 : (Φ (INN (s / 4)))⁻¹ * Φ (INN (s' / 4)) =
        kX α β (s % 4) * (kX α β (s' % 4))⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq, mul_assoc]
      change _ * σ s' = _
      rw [← e]
      change (Φ (INN (s / 4)))⁻¹ * (Φ (INN (s / 4)) * kX α β (s % 4)) = _
      rw [← mul_assoc, inv_mul_cancel, one_mul]
    have hI : kX α β (s % 4) * (kX α β (s' % 4))⁻¹ ∈ (MulAut.conj : H →* MulAut H).range := by
      rw [← e2]
      exact mul_mem (inv_mem (hinnΦ _ hu)) (hinnΦ _ hu')
    have hV : kX α β (s % 4) * (kX α β (s' % 4))⁻¹ ∈ Subgroup.closure ({α, β} : Set (MulAut H)) :=
      mul_mem (kX_mem α β _) (inv_mem (kX_mem α β _))
    have h1 : kX α β (s % 4) * (kX α β (s' % 4))⁻¹ = 1 := by
      rcases E613.closure_pair_subset hα.1 hβ.1 hc hV with h | h | h | h
      · exact h
      · rw [h] at hI
        exact absurd hI hα.2.2
      · rw [h] at hI
        exact absurd hI hβ.2.2
      · rw [h] at hI
        exact absurd hI hnn
    have hbb := hXinj _ hb _ hb' (mul_inv_eq_one.1 h1)
    have huu : Φ (INN (s / 4)) = Φ (INN (s' / 4)) := by
      have e3 : Φ (INN (s / 4)) * kX α β (s % 4) = Φ (INN (s' / 4)) * kX α β (s' % 4) := e
      rw [hbb] at e3
      exact mul_right_cancel e3
    have := inn_inj' hinn _ hu _ hu'
      (pd.inj _ (eInnK_spec hinn _ hu).1 _ (eInnK_spec hinn _ hu').1 huu)
    omega
  have hσinjOn : Set.InjOn σ ↑(Finset.range 64) := fun s hs s' hs' e =>
    hσinj s (Finset.mem_range.1 hs) s' (Finset.mem_range.1 hs') e
  have hSset : (Sg : Set (MulAut H)) = ↑((Finset.range 64).image σ) := by
    ext ψ
    rw [SetLike.mem_coe, Finset.coe_image, Finset.coe_range]
    constructor
    · intro hψ
      obtain ⟨s, hs, e⟩ := hσsurj ψ hψ
      exact ⟨s, hs, e⟩
    · rintro ⟨s, hs, rfl⟩
      exact hσmem s hs
  refine ⟨fun e he => ?_, ?_, ?_, fun ψ hψ hψ2 => ?_⟩
  · obtain ⟨k, hk, rfl⟩ := R.surj e
    have h1 := allN_iff.1 hfix k hk
    rw [hA.elt_eq hk] at he
    have hk' : eG A k = k := R.inj _ _ (hA.lt hk) hk he
    rw [bIf_eq, if_pos (beq_t.2 hk')] at h1
    rw [hB.elt_eq hk, beq_t.1 h1]
  · obtain ⟨e, he, hg⟩ := eAnyN_iff.1 hge
    have hAe := hA.lt he
    have hBe := hB.lt he
    have hABe := hA.lt hBe
    obtain ⟨f0, f1, f2, f3⟩ := eKlGen_fields (A := A) (B := B) (by omega : e < 64) (by omega)
      (by omega) (by omega)
    refine ⟨elt e, top_of_gen R hM (S := eKlGen A B e) (k := 4) (fun j hj => ?_) hg
      fun j hj => ?_⟩
    · interval_cases j
      · rw [f0]; exact he
      · rw [f1]; exact hAe
      · rw [f2]; exact hBe
      · rw [f3]; exact hABe
    · interval_cases j
      · rw [f0]
        exact Subgroup.subset_closure (by simp)
      · rw [f1, ← hA.elt_eq he]
        exact Subgroup.subset_closure (by simp)
      · rw [f2, ← hB.elt_eq he]
        exact Subgroup.subset_closure (by simp)
      · rw [f3, ← hA.elt_eq hBe, ← hB.elt_eq he]
        exact Subgroup.subset_closure (by simp)
  · have e1 : Nat.card ↥Sg = (Sg : Set (MulAut H)).ncard := Nat.card_coe_set_eq _
    rw [e1, hSset, Set.ncard_coe_finset, Finset.card_image_of_injOn hσinjOn, Finset.card_range]
  · obtain ⟨s, hs, rfl⟩ := hσsurj ψ hψ
    have hsq : eKlSq GN kg T INN A B (eC A B) s = true := by
      unfold eKlSq
      rw [allN_iff]
      intro j hj
      rw [strictB_eq]
      apply beq_t.2
      rw [← hσact s hs _ (hS j hj), ← hσact s hs _ (sg_lt R _ _), ← sg_mul, hψ2, sg_one R (hS j hj)]
    have h16 := allN_iff.1 hcnt s hs
    rw [bIf_eq, if_pos hsq, Nat.ble_eq, eCnt_eq_card] at h16
    refine le_trans h16 ?_
    have hinjF : Set.InjOn σ ↑((Finset.range 64).filter fun s' =>
        eKlComm GN kg T INN A B (eC A B) s s' = true) :=
      hσinjOn.mono fun s' hs' => by
        rw [Finset.coe_filter] at hs'
        exact hs'.1
    rw [← Set.ncard_coe_finset, ← hinjF.ncard_image]
    have e1 : Nat.card ↥(Sg ⊓ Subgroup.centralizer ({σ s} : Set (MulAut H))) =
        ((Sg ⊓ Subgroup.centralizer ({σ s} : Set (MulAut H)) : Subgroup (MulAut H)) :
          Set (MulAut H)).ncard := Nat.card_coe_set_eq _
    rw [e1]
    refine Set.ncard_le_ncard (fun ψ' hψ' => ?_) (Set.toFinite _)
    obtain ⟨s', hs', rfl⟩ := hψ'
    rw [Finset.coe_filter] at hs'
    obtain ⟨hs'r, hcomm⟩ := hs'
    have hs'64 : s' < 64 := Finset.mem_range.1 hs'r
    rw [SetLike.mem_coe, Subgroup.mem_inf]
    refine ⟨hσmem s' hs'64, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    refine mulAut_ext_sg R (sg_eq_of_gen R hM hS hgen _ _ fun j hj => ?_)
    have h1 := allN_iff.1 hcomm j hj
    rw [strictB_eq] at h1
    rw [sg_mul R (σ s) (σ s'), sg_mul R (σ s') (σ s), hσact s' hs'64 _ (hS j hj),
      hσact s hs _ (hS j hj),
      hσact s hs _ (hσlt _ hs'64 _ (hS j hj)), hσact s' hs'64 _ (hσlt _ hs _ (hS j hj))]
    exact beq_t.1 h1

theorem klein_of_checks (hkl : e613KlK ET GN kg f PR T nr REP nv IV INN = true)
    {φ₁ φ₂ : MulAut H} (h₁ : IsB π φ₁) (h₂ : IsB π φ₂) (hc : φ₁ * φ₂ = φ₂ * φ₁) (hne : φ₁ ≠ φ₂)
    (hnn : φ₁ * φ₂ ∉ (MulAut.conj : H →* MulAut H).range) : KleinF φ₁ φ₂ := by
  have := finite_mulAut R
  have h1 : φ₁ ≠ 1 := fun e => h₁.2.2 (e ▸ one_mem _)
  obtain ⟨q, -, -, hl, hconj⟩ := inv_pos R pd hcan hcls h₁.1 h1
  have hrep := eClsK_rep hcls _ hl
  obtain ⟨χ, hχ⟩ : ∃ χ, χ = Φ (ICJ q) := ⟨_, rfl⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = Φ (REP (ICL q)) := ⟨_, rfl⟩
  rw [← hχ, ← hρ] at hconj
  have hρ' : ρ = χ⁻¹ * φ₁ * χ := by rw [mul_assoc, ← hconj, ← mul_assoc, inv_mul_cancel, one_mul]
  have hconj2 : χ * (χ⁻¹ * φ₂ * χ) = φ₂ * χ := by group
  have hbρ := isB_conj hconj h₁
  have hb2 := isB_conj hconj2 h₂
  have h2' : χ⁻¹ * φ₂ * χ ≠ 1 := fun e => hb2.2.2 (e ▸ one_mem _)
  obtain ⟨q', hq', hφq', -, -⟩ := inv_pos R pd hcan hcls hb2.1 h2'
  have hiv := (eClsK_spec hcls).2 q' hq'
  have hA : Acts R ρ (T (REP (ICL q))) := by
    rw [hρ]
    exact pd.acts _ hrep
  have hB : Acts R (χ⁻¹ * φ₂ * χ) (T (IV q')) := by
    rw [← hφq']
    exact pd.acts _ hiv.1
  have hcomm : ρ * (χ⁻¹ * φ₂ * χ) = (χ⁻¹ * φ₂ * χ) * ρ := by
    rw [hρ']
    calc χ⁻¹ * φ₁ * χ * (χ⁻¹ * φ₂ * χ) = χ⁻¹ * (φ₁ * φ₂) * χ := by group
      _ = χ⁻¹ * (φ₂ * φ₁) * χ := by rw [hc]
      _ = χ⁻¹ * φ₂ * χ * (χ⁻¹ * φ₁ * χ) := by group
  have hne' : ρ ≠ χ⁻¹ * φ₂ * χ := fun e => hne (by
    rw [hρ'] at e
    calc φ₁ = χ * (χ⁻¹ * φ₁ * χ) * χ⁻¹ := by group
      _ = χ * (χ⁻¹ * φ₂ * χ) * χ⁻¹ := by rw [e]
      _ = φ₂ := by group)
  have hnn' : ρ * (χ⁻¹ * φ₂ * χ) ∉ (MulAut.conj : H →* MulAut H).range := fun hm => hnn (by
    have e : χ * (ρ * (χ⁻¹ * φ₂ * χ)) * χ⁻¹ = φ₁ * φ₂ := by
      rw [hρ']
      group
    rw [← e]
    exact inn_conj hm)
  have hBA := eBInv_of_isB R hM pd hcan htup hpr hπ hker hinn hcls hrep hρ.symm hbρ
  have hBB := eBInv_of_isB R hM pd hcan htup hpr hπ hker hinn hcls hiv.1 hφq' hb2
  have hpart : eKlPart ET GN kg PR (T (REP (ICL q))) (T (IV q')) = true := by
    unfold eKlPart
    rw [bAnd_eq, bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, bIf_eq,
      bIf_eq]
    refine ⟨hBB, ?_, (hA.comm_iff hM htup hB).1 hcomm, ?_⟩
    · rw [if_neg fun e => hne' (hA.ext hB fun a _ => by rw [beq_t.1 e])]
    · rw [if_neg fun e => hnn' ((pi_ker R hM (tup_ctr htup) hpr pd hπ hker hinn _).1
        ((pi_eq_one_iff R hM hpr hπ (hA.mul hB)).2 e))]
  have hk := allN_iff.1 hkl (ICL q) hl
  rw [strictB_eq, bIf_eq, if_pos hBA] at hk
  have hk2 := allN_iff.1 hk q' hq'
  rw [strictB_eq, bIf_eq, if_pos hpart] at hk2
  have hKF := klein_of_check R hM pd hcan htup hpr hπ hker hinn hcls hA hB hbρ hb2 hcomm hne' hnn'
    hk2
  have hKF' := klein_conj χ hKF
  have e1 : χ * ρ * χ⁻¹ = φ₁ := by rw [hconj, mul_inv_cancel_right]
  have e2 : χ * (χ⁻¹ * φ₂ * χ) * χ⁻¹ = φ₂ := by group
  rwa [e1, e2] at hKF'

end Main

theorem eFacts613_of_checks {G : Type u} [Group G] {E : Subgroup G} {t : G} {mulE : ℕ → ℕ → ℕ}
    {eltE : ℕ → G} {ET : ℕ → ℕ} (hL : ELabelling E t mulE 21 eltE)
    (hET : ∀ a < 32, ∀ b < 32, mulE a b = eMul ET a b) {T REP IV ICL ICJ INN INE : ℕ → ℕ}
    {GN kg f c PR nr nv : ℕ} (hrec : RecOK.{u} ET 1920 T)
    (hcan : ∀ i < 1920, canonK 32 6 63 192 (T i) = true) (htup : eTupK ET GN kg f c = true)
    (hpr : ePrK ET PR = true) (hker : eKerK ET PR 1920 T 16 INN = true)
    (hinn : eInnK ET 1920 T 16 INN INE = true) (hcls : eClsK 1920 T nr REP nv IV ICL ICJ = true)
    (hfix : e613FixK ET PR T nr REP = true)
    (hkl : e613KlK ET GN kg f PR T nr REP nv IV INN = true) : EFacts613 E t := by
  obtain ⟨elt, R, -⟩ := realizes_of_labelling hL
  have hM : ∀ a < 32, ∀ b < 32, mt (tab2 32 mulE) a b = eMul ET a b := fun a ha b hb =>
    (mt_tab2 mulE ha hb).trans (hET a ha b hb)
  obtain ⟨Φ, pd⟩ := exists_posData R hM hrec
  have hc := tup_ctr htup
  obtain ⟨π, hπ⟩ := exists_pi R hM hc hpr
  refine ⟨π, ⟨pi_surj R hM hc hpr pd hπ hker hinn (hrec _ _ _ R hM).2.2,
    fun φ => pi_ker R hM hc hpr pd hπ hker hinn φ⟩,
    fun φ hφ => (fix_coc_of_checks R hM pd hcan htup hpr hπ hker hinn hcls hfix hφ).1,
    fun φ hφ => (fix_coc_of_checks R hM pd hcan htup hpr hπ hker hinn hcls hfix hφ).2,
    fun φ₁ φ₂ h₁ h₂ hc12 hne hnn =>
      klein_of_checks R hM pd hcan htup hpr hπ hker hinn hcls hkl h₁ h₂ hc12 hne hnn⟩

end CFSG.KS.EAut

end
