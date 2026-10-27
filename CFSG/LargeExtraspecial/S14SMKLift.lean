module

public import CFSG.LargeExtraspecial.S14SMKE23aModel
public import CFSG.LargeExtraspecial.S14SMJWeak

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.SMK

open Subgroup CFSG.Open CFSG.SmithE CFSG.F4.Native CFSG.LargeExtraspecial.SMod20

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def Phi (S : Setting G) (φ : S.Qt ≃ₗ[ZMod 2] V) :
    S.M →* (V ≃ₗ[ZMod 2] V) where
  toFun g := φ.symm.trans (((S.ρ g : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).trans φ)
  map_one' := by
    ext v
    simp
  map_mul' g h := by
    ext v
    simp only [map_mul, Subgroup.coe_mul, LinearEquiv.trans_apply, LinearEquiv.mul_apply,
      LinearEquiv.symm_apply_apply]

variable {S : Setting G} {φ : S.Qt ≃ₗ[ZMod 2] V}

theorem Phi_apply (g : S.M) (v : V) :
    Phi S φ g v = φ (((S.ρ g : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (φ.symm v)) := rfl

theorem Phi_cl (g : S.M) {y : G} (hy : y ∈ S.QG) :
    Phi S φ g (φ (S.cl y)) = φ (S.cl ((g : G) * y * (g : G)⁻¹)) := by
  rw [Phi_apply, LinearEquiv.symm_apply_apply, S.ρ_cl g hy]

theorem Phi_eq_one_iff (g : S.M) : Phi S φ g = 1 ↔ (g : G) ∈ S.QG := by
  rw [← S.ρ_eq_one_iff]
  constructor
  · intro h
    apply Subtype.ext
    ext w
    have := congrArg (fun f : V ≃ₗ[ZMod 2] V => φ.symm (f (φ w))) h
    simpa [Phi_apply] using this
  · intro h
    ext v
    simp [Phi_apply, h]

theorem code_decode {c : Nat} (hc : c < 2 ^ 20) : SMG.code (decode c) = c := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [SMG.testBit_code]
  split_ifs with hi
  · rw [decode_apply]
    cases c.testBit i <;> rfl
  · exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num)
      (by omega)))).symm

theorem acts_iff {x : G} (hx : x ∈ S.M) {k : Nat}
    (hk : k < 693) :
    (∀ y ∈ S.QG, SMG.code (φ (S.cl (x * y * x⁻¹))) =
      applyCols (tvCols k) (SMG.code (φ (S.cl y)))) ↔ Phi S φ ⟨x, hx⟩ = tvEquiv k := by
  constructor
  · intro h
    ext v : 1
    obtain ⟨y, hy, hyv⟩ := S.exists_cl (φ.symm v)
    have hv : v = φ (S.cl y) := by rw [hyv, LinearEquiv.apply_symm_apply]
    rw [hv, Phi_cl ⟨x, hx⟩ hy, ← decode_code (φ (S.cl (x * y * x⁻¹))), h y hy,
      ← tvEquiv_decode hk, decode_code]
  · intro h y hy
    have e := congrArg (fun f : V ≃ₗ[ZMod 2] V => f (φ (S.cl y))) h
    simp only [Phi_cl ⟨x, hx⟩ hy] at e
    rw [e, ← decode_code (φ (S.cl y)), tvEquiv_decode hk, code_decode (applyCols_tvCols_lt hk _),
      decode_code]

theorem exists_word_conj
    (h5 : ∀ k < 693, ∃ m : S.M, Phi S φ m = tvEquiv k) (w : List Nat)
    (hw : ∀ j ∈ w, j < 693) :
    ∃ g : S.M, ∀ a < 693, Phi S φ g * tvEquiv a * (Phi S φ g)⁻¹ = tvEquiv (wordImg w a) := by
  induction w with
  | nil => exact ⟨1, fun a _ => by rw [map_one, one_mul, inv_one, mul_one, wordImg_nil]⟩
  | cons j w ih =>
    obtain ⟨g', hg'⟩ := ih fun j' h => hw j' (List.mem_cons_of_mem _ h)
    have hj := hw j List.mem_cons_self
    obtain ⟨m, hm⟩ := h5 j hj
    refine ⟨g' * m, fun a ha => ?_⟩
    rw [wordImg_cons, ← hg' _ (ptImg_lt hj ha), ← tvEquiv_conj_inv hj ha, map_mul, hm]
    group

theorem commute_tvEquiv_of_herm
    {k l : Nat} (hkl : k < l) (hl : l < 693) (h0 : hermC uPts[k]! uPts[l]! = 0) :
    Commute (tvEquiv k) (tvEquiv l) := by
  have hc := (SMG.pair_rel hkl hl).1 h0
  have hk : k < 693 := by omega
  show tvEquiv k * tvEquiv l = tvEquiv l * tvEquiv k
  apply linearEquiv_ext_single
  intro m
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ← decode_two_pow, tvEquiv_decode hl,
    tvEquiv_decode hk, tvEquiv_decode hk, tvEquiv_decode hl,
    hc _ (Nat.pow_lt_pow_right (by norm_num) m.2)]

theorem herm_ne_of_orderOf
    {T U : S.M} (h3 : orderOf ((T : G) * (U : G)) = 3) {l : Nat} (hl : l < 693)
    (hT : Phi S φ T = tvEquiv 0) (hU : Phi S φ U = tvEquiv l) : hermC uPts[0]! uPts[l]! ≠ 0 := by
  intro h0
  have hnot := SMJ.mul_not_mem_QG S h3
  have hl0 : l ≠ 0 := by
    rintro rfl
    apply hnot
    have : Phi S φ (T * U) = 1 := by rw [map_mul, hT, hU, tvEquiv_mul_self (by norm_num)]
    exact (Phi_eq_one_iff (T * U)).mp this
  have hc := commute_tvEquiv_of_herm (Nat.pos_of_ne_zero hl0) hl h0
  have h2 : (((T * U) ^ 2 : S.M) : G) ∈ S.QG := by
    refine (Phi_eq_one_iff (φ := φ) _).mp ?_
    rw [map_pow, map_mul, hT, hU, sq, ← mul_assoc, mul_assoc (tvEquiv 0), ← hc.eq, ← mul_assoc,
      tvEquiv_mul_self (by norm_num), one_mul, tvEquiv_mul_self hl]
  have h3' : ((T : G) * (U : G)) ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one _
  apply hnot
  have e : (T : G) * (U : G) = ((((T * U) ^ 2 : S.M) : G))⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    push_cast
    rw [← pow_succ', h3']
  rw [e]
  exact S.QG.inv_mem h2

theorem exists_conj_std
    (h4 : ∀ x : G, IsConj S.z x → ∀ hx : x ∈ S.M, x ∉ S.QG →
      ∃ k < 693, Phi S φ ⟨x, hx⟩ = tvEquiv k)
    (h5 : ∀ k < 693, ∃ m : S.M, Phi S φ m = tvEquiv k) {t u : G} (C : SMJ.Cfg S t u) :
    ∃ g : S.M, Phi S φ g * Phi S φ ⟨t, C.htM⟩ * (Phi S φ g)⁻¹ = tvEquiv 0 ∧
      Phi S φ g * Phi S φ ⟨u, C.huM⟩ * (Phi S φ g)⁻¹ = tvEquiv 1 := by
  obtain ⟨k, hk, hkt⟩ := h4 t C.ht C.htM C.htQ
  obtain ⟨l, hl, hlu⟩ := h4 u C.hu C.huM C.huQ
  obtain ⟨w₁, hw₁, hw₁k⟩ := exists_ptWord hk
  obtain ⟨g₁, hg₁⟩ := exists_word_conj h5 w₁ hw₁
  have hl' : wordImg w₁ l < 693 := wordImg_lt hw₁ hl
  have hne : hermC uPts[0]! uPts[wordImg w₁ l]! ≠ 0 := by
    refine herm_ne_of_orderOf (φ := φ) (T := g₁ * ⟨t, C.htM⟩ * g₁⁻¹)
      (U := g₁ * ⟨u, C.huM⟩ * g₁⁻¹)
      ?_ hl' ?_ ?_
    · have e : ((g₁ * ⟨t, C.htM⟩ * g₁⁻¹ : S.M) : G) * ((g₁ * ⟨u, C.huM⟩ * g₁⁻¹ : S.M) : G) =
          (g₁ : G) * (t * u) * (g₁ : G)⁻¹ := by
        push_cast
        group
      rw [e, show (g₁ : G) * (t * u) * (g₁ : G)⁻¹ = MulAut.conj (g₁ : G) (t * u) from rfl,
        MulEquiv.orderOf_eq]
      exact C.h3
    · rw [map_mul, map_mul, map_inv, hkt, hg₁ k hk, hw₁k]
    · rw [map_mul, map_mul, map_inv, hlu, hg₁ l hl]
  obtain ⟨w₂, hw₂, hw₂l⟩ := exists_pairWord hl' hne
  obtain ⟨g₂, hg₂⟩ := exists_word_conj h5 w₂ fun j h => (hw₂ j h).1
  refine ⟨g₂ * g₁, ?_, ?_⟩
  · rw [map_mul, hkt, mul_inv_rev, show Phi S φ g₂ * Phi S φ g₁ * tvEquiv k *
      ((Phi S φ g₁)⁻¹ * (Phi S φ g₂)⁻¹) = Phi S φ g₂ * (Phi S φ g₁ * tvEquiv k *
        (Phi S φ g₁)⁻¹) * (Phi S φ g₂)⁻¹ by group, hg₁ k hk, hw₁k, hg₂ 0 (by norm_num),
      wordImg_zero_of_fix fun j h => (hw₂ j h).2]
  · rw [map_mul, hlu, mul_inv_rev, show Phi S φ g₂ * Phi S φ g₁ * tvEquiv l *
      ((Phi S φ g₁)⁻¹ * (Phi S φ g₂)⁻¹) = Phi S φ g₂ * (Phi S φ g₁ * tvEquiv l *
        (Phi S φ g₁)⁻¹) * (Phi S φ g₂)⁻¹ by group, hg₁ l hl, hg₂ _ hl', hw₂l]

@[expose] def Clauses (S : Setting G) (t u : G) : Prop :=
  (∀ c ∈ S.M, Commute c t → Commute c u →
    (∀ q ∈ S.QG, Commute q t → Commute q u → Commute c q) → c ∈ S.QG) ∧
  (∀ P : Subgroup G, P ≤ S.M → (∀ p ∈ P, Commute p t ∧ Commute p u) →
    (∀ c ∈ S.M, Commute c t → Commute c u → ∀ p ∈ P, c * p * c⁻¹ ∈ P) →
      IsPGroup 2 P → P ≤ S.QG) ∧
  (∀ R : Subgroup G, S.z ∈ R → R ≤ S.QG → (∀ r ∈ R, Commute r t ∧ Commute r u) →
    (∀ c ∈ S.M, Commute c t → Commute c u → ∀ r ∈ R, c * r * c⁻¹ ∈ R) →
      R = zpowers S.z ∨ ∀ q ∈ S.QG, Commute q t → Commute q u → q ∈ R) ∧
  (∃ y : G, IsConj S.z y ∧ y ∈ S.M ∧ y ∉ S.QG ∧ Commute y t ∧ Commute y u)

omit [Finite G] in
theorem commute_conj_iff' (g a b : G) :
    Commute (g * a * g⁻¹) (g * b * g⁻¹) ↔ Commute a b := by
  have h := SMJ.commute_conj_iff g⁻¹ (a := a) (b := b)
  simpa only [inv_inv] using h

omit [Finite G] in
theorem conj_conj (g x : G) : g⁻¹ * (g * x * g⁻¹) * g = x := by group

omit [Finite G] in
theorem conj_conj' (g x : G) : g * (g⁻¹ * x * g) * g⁻¹ = x := by group

omit [Finite G] in
theorem conj_mem_M {g x : G} (hg : g ∈ S.M) (hx : x ∈ S.M) : g * x * g⁻¹ ∈ S.M :=
  S.M.mul_mem (S.M.mul_mem hg hx) (S.M.inv_mem hg)

omit [Finite G] in
theorem conj_mem_QG_inv {g x : G} (hg : g ∈ S.M) (hx : x ∈ S.QG) : g⁻¹ * x * g ∈ S.QG := by
  have := S.conj_mem_QG (S.M.inv_mem hg) hx
  rwa [inv_inv] at this

omit [Finite G] in
theorem Clauses.of_conj {t u g : G} (hg : g ∈ S.M)
    (h : Clauses S (g * t * g⁻¹) (g * u * g⁻¹)) : Clauses S t u := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hQ' : ∀ {x : G}, g * x * g⁻¹ ∈ S.QG → x ∈ S.QG := fun hx => by
    have := conj_mem_QG_inv hg hx
    rwa [conj_conj] at this
  have hM' : ∀ {x : G}, x ∈ S.M → g⁻¹ * x * g ∈ S.M := fun hx => by
    have := conj_mem_M (S.M.inv_mem hg) hx
    rwa [inv_inv] at this
  have hc' : ∀ {x y : G}, Commute (g⁻¹ * x * g) y ↔ Commute x (g * y * g⁻¹) := fun {x y} => by
    rw [← commute_conj_iff' g, conj_conj']
  refine ⟨fun c hcM hct hcu hcq => ?_, fun P hPM hPc hPn hP2 => ?_,
    fun R hzR hRQ hRc hRn => ?_, ?_⟩
  ·
    refine hQ' (h1 _ (conj_mem_M hg hcM) ((commute_conj_iff' g c t).mpr hct)
      ((commute_conj_iff' g c u).mpr hcu) fun q' hq' hqt hqu => ?_)
    have hq := conj_mem_QG_inv hg hq'
    have e := hcq _ hq (hc'.mpr hqt) (hc'.mpr hqu)
    rw [← commute_conj_iff' g, conj_conj'] at e
    exact e
  ·
    set P' := P.map (MulAut.conj g).toMonoidHom with hP'
    have hmem : ∀ {x : G}, x ∈ P' ↔ g⁻¹ * x * g ∈ P := fun {x} => by
      rw [hP', Subgroup.mem_map]
      constructor
      · rintro ⟨p, hp, rfl⟩
        simpa [MulAut.conj_apply, conj_conj] using hp
      · intro hx
        exact ⟨_, hx, by simp [MulAut.conj_apply, conj_conj']⟩
    have hle := h2 P' (fun x hx => by
        have := conj_mem_M hg (hPM (hmem.mp hx))
        rwa [conj_conj'] at this)
      (fun x hx => by
        obtain ⟨h1, h2⟩ := hPc _ (hmem.mp hx)
        exact ⟨hc'.mp h1, hc'.mp h2⟩)
      (fun c hcM hct hcu x hx => by
        apply hmem.mpr
        have := hPn _ (hM' hcM) (hc'.mpr hct) (hc'.mpr hcu) _ (hmem.mp hx)
        rw [show g⁻¹ * c * g * (g⁻¹ * x * g) * (g⁻¹ * c * g)⁻¹ = g⁻¹ * (c * x * c⁻¹) * g by
          group] at this
        exact this)
      (hP2.map _)
    intro p hp
    apply hQ'
    exact hle (hmem.mpr (by rwa [conj_conj]))
  ·
    set R' := R.map (MulAut.conj g).toMonoidHom with hR'
    have hmem : ∀ {x : G}, x ∈ R' ↔ g⁻¹ * x * g ∈ R := fun {x} => by
      rw [hR', Subgroup.mem_map]
      constructor
      · rintro ⟨r, hr, rfl⟩
        simpa [MulAut.conj_apply, conj_conj] using hr
      · intro hx
        exact ⟨_, hx, by simp [MulAut.conj_apply, conj_conj']⟩
    have hgz : g⁻¹ * S.z * g = S.z := by
      have := S.z_comm hg
      calc g⁻¹ * S.z * g = g⁻¹ * (S.z * g) := by group
        _ = g⁻¹ * (g * S.z) := by rw [this]
        _ = S.z := by group
    rcases h3 R' (hmem.mpr (by rw [hgz]; exact hzR))
      (fun x hx => by
        have := S.conj_mem_QG hg (hRQ (hmem.mp hx))
        rwa [conj_conj'] at this)
      (fun x hx => by
        obtain ⟨h1, h2⟩ := hRc _ (hmem.mp hx)
        exact ⟨hc'.mp h1, hc'.mp h2⟩)
      (fun c hcM hct hcu x hx => by
        apply hmem.mpr
        have := hRn _ (hM' hcM) (hc'.mpr hct) (hc'.mpr hcu) _ (hmem.mp hx)
        rw [show g⁻¹ * c * g * (g⁻¹ * x * g) * (g⁻¹ * c * g)⁻¹ = g⁻¹ * (c * x * c⁻¹) * g by
          group] at this
        exact this) with hR | hR
    · left
      ext x
      constructor
      · intro hx
        have hx' : g * x * g⁻¹ ∈ R' := hmem.mpr (by rwa [conj_conj])
        rw [hR] at hx'
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx'
        refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
        have hcz : Commute g S.z := S.z_comm hg
        calc S.z ^ n = g⁻¹ * S.z ^ n * g := by
              rw [mul_assoc, ← (hcz.zpow_right n).eq, ← mul_assoc, inv_mul_cancel, one_mul]
          _ = x := by rw [hn, conj_conj]
      · intro hx
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        exact R.zpow_mem hzR n
    · right
      intro q hq hqt hqu
      have := hR _ (S.conj_mem_QG hg hq) ((commute_conj_iff' g q t).mpr hqt)
        ((commute_conj_iff' g q u).mpr hqu)
      rw [hmem, conj_conj] at this
      exact this
  ·
    obtain ⟨y, hy, hyM, hyQ, hyt, hyu⟩ := h4
    refine ⟨g⁻¹ * y * g, hy.trans (isConj_iff.mpr ⟨g⁻¹, by group⟩), hM' hyM, fun h => hyQ ?_,
      hc'.mpr hyt, hc'.mpr hyu⟩
    have := S.conj_mem_QG hg h
    rwa [conj_conj'] at this

@[expose] noncomputable def liftSet (S : Setting G) (φ : S.Qt ≃ₗ[ZMod 2] V)
    (r : Nat) (θ : S.M)
    (hθ : Commute (Phi S φ θ) (tvEquiv r)) :
    SubMulAction (zpowers (ConjAct.toConjAct θ)) S.M where
  carrier := {x | IsConj S.z (x : G) ∧ Phi S φ x = tvEquiv r}
  smul_mem' := by
    rintro ⟨h, hh⟩ x ⟨hxz, hxr⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    have e : ((⟨ConjAct.toConjAct θ ^ n, hh⟩ : zpowers (ConjAct.toConjAct θ)) • x) =
        θ ^ n * x * (θ ^ n)⁻¹ := by
      show (ConjAct.toConjAct θ ^ n) • x = _
      rw [ConjAct.smul_def, map_zpow, ConjAct.ofConjAct_toConjAct]
    simp only [Set.mem_ofPred_eq]
    rw [e]
    refine ⟨hxz.trans (isConj_iff.mpr ⟨(θ ^ n : S.M), by push_cast; rfl⟩), ?_⟩
    rw [map_mul, map_mul, map_inv, hxr, map_zpow, ((hθ.zpow_left n).eq), mul_assoc,
      mul_inv_cancel, mul_one]

theorem mem_liftSet {r : Nat} {θ : S.M}
    {hθ : Commute (Phi S φ θ) (tvEquiv r)} {x : S.M} :
    x ∈ liftSet S φ r θ hθ ↔ IsConj S.z (x : G) ∧ Phi S φ x = tvEquiv r := Iff.rfl

omit [Finite G] in
theorem coe_mem_QG_iff {q : S.M} : (q : G) ∈ S.QG ↔ q ∈ S.Q := by
  rw [S.mem_QG_iff]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨q.2, h⟩⟩

theorem not_three_dvd_card_liftSet (h34b : SmithE34b)
    [IsSimpleGroup G] (hw : S.width = 10) (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6))
    {r : Nat} {θ : S.M} {hθ : Commute (Phi S φ θ) (tvEquiv r)} {y₀ : S.M}
    (hy₀ : y₀ ∈ liftSet S φ r θ hθ) (hy₀Q : (y₀ : G) ∉ S.QG) :
    ¬ 3 ∣ Nat.card (liftSet S φ r θ hθ) := by
  set Q' : Subgroup (ConjAct S.M) := S.Q.map (ConjAct.toConjAct : S.M ≃* ConjAct S.M).toMonoidHom
  obtain ⟨hy₀z, hy₀r⟩ := hy₀
  have hset : ∀ x : S.M, x ∈ liftSet S φ r θ hθ ↔ x ∈ MulAction.orbit Q' y₀ := by
    intro x
    rw [mem_liftSet]
    constructor
    · rintro ⟨hxz, hxr⟩
      have hQ : (y₀ : G)⁻¹ * (x : G) ∈ S.QG := by
        have : Phi S φ (y₀⁻¹ * x) = 1 := by rw [map_mul, map_inv, hxr, hy₀r, inv_mul_cancel]
        exact (Phi_eq_one_iff _).mp this
      obtain ⟨q, hq, hqx⟩ := h34b G S hw hU y₀ x hy₀z hxz y₀.2 hy₀Q hQ
      have hqM : q⁻¹ ∈ S.M := S.QG_le_M (S.QG.inv_mem hq)
      refine ⟨⟨ConjAct.toConjAct (⟨q⁻¹, hqM⟩ : S.M),
        ⟨_, coe_mem_QG_iff.mp (S.QG.inv_mem hq), rfl⟩⟩, ?_⟩
      apply Subtype.ext
      show ((ConjAct.toConjAct (⟨q⁻¹, hqM⟩ : S.M) • y₀ : S.M) : G) = x
      rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, hqx]
      push_cast
      rw [inv_inv]
    · rintro ⟨⟨c, hc⟩, rfl⟩
      obtain ⟨q₀, hq₀, rfl⟩ := Subgroup.mem_map.mp hc
      have hq₀Q : (q₀ : G) ∈ S.QG := coe_mem_QG_iff.mpr hq₀
      have e : ((⟨_, hc⟩ : Q') • y₀ : S.M) = q₀ * y₀ * q₀⁻¹ := by
        show ConjAct.toConjAct q₀ • y₀ = _
        rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct]
      show IsConj S.z ((((⟨_, hc⟩ : Q') • y₀ : S.M)) : G) ∧ Phi S φ ((⟨_, hc⟩ : Q') • y₀) = _
      rw [e]
      refine ⟨hy₀z.trans (isConj_iff.mpr ⟨(q₀ : G), by push_cast; rfl⟩), ?_⟩
      rw [map_mul, map_mul, map_inv, (Phi_eq_one_iff q₀).mpr hq₀Q, hy₀r, one_mul, inv_one,
        mul_one]
  have hcard : Nat.card (liftSet S φ r θ hθ) = Nat.card (MulAction.orbit Q' y₀) :=
    Nat.card_congr (Equiv.subtypeEquivRight hset)
  have hQ2 : IsPGroup 2 Q' := S.extraspecial.1.map _
  obtain ⟨n, hn⟩ := hQ2.card_orbit y₀
  rw [hcard, hn]
  intro h3
  have := (Nat.prime_three.dvd_of_dvd_pow h3)
  omega

omit [Finite G] in
theorem conj_theta_tyt {t u y : G} (htt : t * t = 1) (huu : u * u = 1)
    (h3 : (t * u) ^ 3 = 1) (hy : t * u * y * (t * u)⁻¹ = y) :
    t * u * (t * y * t) * (t * u)⁻¹ = t * y * t := by
  have hat : t * u * t * (t * u)⁻¹ = u := SMJ.conj_theta_t htt huu h3
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  calc t * u * (t * y * t) * (t * u)⁻¹
      = (t * u * t * (t * u)⁻¹) * (t * u * y * (t * u)⁻¹) * (t * u * t * (t * u)⁻¹) := by group
    _ = u * y * u := by rw [hat, hy]
    _ = t * (t * u * y * (t * u)⁻¹) * t := by
        rw [mul_inv_rev, hti, hui]
        calc u * y * u = (t * t) * u * y * u * (t * t) := by rw [htt, one_mul, mul_one]
          _ = t * (t * u * y * (u * t)) * t := by group
    _ = t * y * t := by rw [hy]

theorem exists_lift
    (hM : SmithE22Module) (h34a : SmithE34a) (h34b : SmithE34b) (h25 : SmithE25)
    (hLoc : SmithU62LocalInput) [IsSimpleGroup G] (hw : S.width = 10)
    (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6))
    (h5 : ∀ k < 693, ∃ m : S.M, Phi S φ m = tvEquiv k) {t u : G} (C : SMJ.Cfg S t u)
    (ht0 : Phi S φ ⟨t, C.htM⟩ = tvEquiv 0) (hu1 : Phi S φ ⟨u, C.huM⟩ = tvEquiv 1)
    {r : Nat} (hr : r ∈ c8Pts) :
    ∃ y : S.M, IsConj S.z (y : G) ∧ (y : G) ∉ S.QG ∧ Commute (y : G) t ∧
      Commute (y : G) u ∧ Phi S φ y = tvEquiv r := by
  obtain ⟨hr693, hr0, hr1⟩ := commute_c8Pts hr
  set T : S.M := ⟨t, C.htM⟩ with hT
  set U : S.M := ⟨u, C.huM⟩ with hU'
  have htt : t * t = 1 := SmithQ.mul_self_eq_one_of_isConj S C.ht
  have huu : u * u = 1 := SmithQ.mul_self_eq_one_of_isConj S C.hu
  have h3p : (t * u) ^ 3 = 1 := by rw [← C.h3]; exact pow_orderOf_eq_one _
  obtain ⟨w, hw', hwr⟩ := exists_ptWord hr693
  obtain ⟨g, hg⟩ := exists_word_conj (φ := φ) h5 w hw'
  have hgr : Phi S φ g * tvEquiv r * (Phi S φ g)⁻¹ = tvEquiv 0 := by rw [hg r hr693, hwr]
  set Y₀ : S.M := g⁻¹ * T * g with hY₀
  have hY₀r : Phi S φ Y₀ = tvEquiv r := by
    rw [hY₀, map_mul, map_mul, map_inv, ht0, ← hgr]
    group
  have hY₀z : IsConj S.z (Y₀ : G) :=
    C.ht.trans (isConj_iff.mpr ⟨(g : G)⁻¹, by rw [hY₀]; push_cast; rw [inv_inv]⟩)
  have hY₀Q : (Y₀ : G) ∉ S.QG := fun h => C.htQ (by
    have := S.conj_mem_QG g.2 h
    rwa [hY₀, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, conj_conj'] at this)
  set Θ : S.M := T * U with hΘ
  have hΘr : Commute (Phi S φ Θ) (tvEquiv r) := by
    rw [hΘ, map_mul, ht0, hu1]
    exact hr0.symm.mul_left hr1.symm
  have hX3 := not_three_dvd_card_liftSet (hθ := hΘr) h34b hw hU ⟨hY₀z, hY₀r⟩ hY₀Q
  have hH : IsPGroup 3 (zpowers (ConjAct.toConjAct Θ)) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, MulEquiv.orderOf_eq, pow_one,
      ← orderOf_injective S.M.subtype Subtype.val_injective]
    exact C.h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨Y₁, hY₁z, hY₁r⟩, hfix⟩ := hH.nonempty_fixed_point_of_prime_not_dvd_card _ hX3
  have hΘY₁ : Θ * Y₁ * Θ⁻¹ = Y₁ := by
    have h1 := congrArg Subtype.val (hfix ⟨ConjAct.toConjAct Θ, mem_zpowers _⟩)
    have h2 : (((⟨ConjAct.toConjAct Θ, mem_zpowers _⟩ : zpowers (ConjAct.toConjAct Θ)) •
        (⟨Y₁, hY₁z, hY₁r⟩ : liftSet S φ r Θ hΘr) : liftSet S φ r Θ hΘr) : S.M) =
        ConjAct.toConjAct Θ • Y₁ := rfl
    rw [h2, ConjAct.smul_def, ConjAct.ofConjAct_toConjAct] at h1
    exact h1
  set y := (Y₁ : G) with hy
  have hyM : y ∈ S.M := Y₁.2
  have hyQ : y ∉ S.QG := fun h => hY₀Q ((Phi_eq_one_iff Y₀).mp (by
    rw [hY₀r, ← hY₁r]
    exact (Phi_eq_one_iff Y₁).mpr h))
  have hθy : t * u * y * (t * u)⁻¹ = y := by
    have := congrArg Subtype.val hΘY₁
    simpa [hΘ, hT, hU'] using this
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  set v := t * y * t with hv
  have hvz : IsConj S.z v := hY₁z.trans (isConj_iff.mpr ⟨t, by rw [hv, hti]⟩)
  have hvM : v ∈ S.M := S.M.mul_mem (S.M.mul_mem C.htM hyM) C.htM
  have hVr : Phi S φ ⟨v, hvM⟩ = tvEquiv r := by
    have e : (⟨v, hvM⟩ : S.M) = T * Y₁ * T⁻¹ := by
      apply Subtype.ext
      show t * y * t = t * y * t⁻¹
      rw [hti]
    rw [e, map_mul, map_mul, map_inv, ht0, hY₁r, hr0.symm.eq, mul_assoc,
      mul_inv_cancel, mul_one]
  have hwQ : y⁻¹ * v ∈ S.QG := by
    have : Phi S φ (Y₁⁻¹ * ⟨v, hvM⟩) = 1 := by
      rw [map_mul, map_inv, hY₁r, hVr, inv_mul_cancel]
    exact (Phi_eq_one_iff _).mp this
  have hθv : t * u * v * (t * u)⁻¹ = v := conj_theta_tyt htt huu h3p hθy
  have hwθ : y⁻¹ * v ∈ centralizer ({t * u} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have e1 : t * u * y⁻¹ * (t * u)⁻¹ = y⁻¹ := by
      rw [show t * u * y⁻¹ * (t * u)⁻¹ = (t * u * y * (t * u)⁻¹)⁻¹ by group, hθy]
    symm
    calc t * u * (y⁻¹ * v) = (t * u * y⁻¹ * (t * u)⁻¹) * (t * u * v * (t * u)⁻¹) * (t * u) := by
          group
      _ = y⁻¹ * v * (t * u) := by rw [e1, hθv]
  have hwH : y⁻¹ * v ∈ S.QG ⊓ SMJ.cent2 t u := by
    rw [← SMJ.cqx_eq_cent2 h25 h34a S hw hU C.ht C.hu C.htM C.huM C.htQ C.huQ C.h3]
    exact mem_inf.mpr ⟨hwQ, hwθ⟩
  obtain ⟨hwt, hwu⟩ := SMJ.mem_cent2.mp (mem_inf.mp hwH).2
  obtain ⟨q, hq, hqw⟩ := SME.exists_commutator_of_coset h34b S hw hU hY₁z hvz hyM hyQ hwQ
  have hw2 : (y⁻¹ * v) ^ 2 = 1 := by
    rw [hqw]
    exact SME.sq_eq_one_of_mem_commutator h34a S hw hU hY₁z hyM hyQ (SME.commutator_mem S y hq)
  have hyi : y⁻¹ = y := SME.inv_eq_of_isConj S hY₁z
  have hwyt : y⁻¹ * v = (y * t) ^ 2 := by rw [hyi, hv, sq]; group
  by_cases hw1 : y⁻¹ * v = 1
  ·
    have hyt : Commute y t := by
      have e : t * y * t = y := by
        have := hw1
        rw [hv, inv_mul_eq_one] at this
        exact this.symm
      show y * t = t * y
      calc y * t = t * y * t * t := by rw [e]
        _ = t * y := by rw [mul_assoc, htt, mul_one]
    have hyθ : Commute y (t * u) := by
      show y * (t * u) = t * u * y
      calc y * (t * u) = t * u * y * (t * u)⁻¹ * (t * u) := by rw [hθy]
        _ = t * u * y := by group
    have hyu : Commute y u := by
      have e : u = t⁻¹ * (t * u) := by group
      rw [e]
      exact hyt.inv_right.mul_right hyθ
    exact ⟨Y₁, hY₁z, hyQ, hyt, hyu, hY₁r⟩
  ·
    exfalso
    have h4 : orderOf (y * t) = 4 := by
      have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := y * t)
        (by rw [pow_one, ← hwyt]; exact hw1)
        (by rw [show (2 : Nat) ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, ← hwyt, hw2])
      simpa using this
    have hwz := (hLoc G S hw hU y t hY₁z C.ht hyM C.htM hyQ).2 h4
    rw [← hwyt] at hwz
    have hweq := SMJ.eq_z_of_mem_cent2 hM S hw hU C hwz hwQ (SMJ.mem_cent2.mpr ⟨hwt, hwu⟩)
    apply h34a G S hw hU y hY₁z hyM hyQ
    have : v = y * S.z := by
      rw [← hweq, ← mul_assoc, ← hyi, mul_inv_cancel, one_mul]
    rw [← this]
    exact hvz

end CFSG.LargeExtraspecial.S14.SMK
