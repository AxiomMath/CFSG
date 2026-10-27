module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCaseLAut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsSetup
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Tools
import CFSG.LocalAnalysis.GL83PartI.I_22_5.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

open CFSG.Open Matrix CFSG.HardMathSupport.Timmesfeld.LinearRank

variable {Ω : Type} [Group Ω] {S : Subgroup Ω}
variable {n : ℕ} {K : Type} [Field K] {H : Subgroup (GL (Fin n) K)}

section Bar

abbrev centerIn (S : Subgroup Ω) : Subgroup Ω := S ⊓ Subgroup.centralizer (S : Set Ω)

instance centerIn_normal [S.Normal] : (centerIn S).Normal :=
  Subgroup.normal_inf_normal _ _

abbrev barMk (S : Subgroup Ω) [S.Normal] : Ω →* Ω ⧸ centerIn S := QuotientGroup.mk' _

abbrev barS (S : Subgroup Ω) [S.Normal] : Subgroup (Ω ⧸ centerIn S) := S.map (barMk S)

instance barS_normal [S.Normal] : (barS S).Normal :=
  Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)

variable [S.Normal] {φ : ↥H →* Ω}

theorem range_barCover (hφS : φ.range = S) : ((barMk S).comp φ).range = barS S := by
  rw [MonoidHom.range_comp, hφS]

theorem ker_barCover (hφS : φ.range = S) {Y : Subgroup (GL (Fin n) K)} (hHY : H ≤ Y)
    (hcent : ∀ c ∈ Y, (∀ k ∈ H, c * k * c⁻¹ * k⁻¹ ∈ StatedScalars (Fin n) K) →
      c ∈ Subgroup.center (GL (Fin n) K))
    (hφk : φ.ker ≤ (StatedScalars (Fin n) K).subgroupOf H) :
    ((barMk S).comp φ).ker = (StatedScalars (Fin n) K).subgroupOf H := by
  have hφH : ∀ k : ↥H, φ k ∈ S := fun k => hφS ▸ ⟨k, rfl⟩
  ext h
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨-, hc⟩
    rw [Subgroup.mem_subgroupOf, CFSG.Open.StatedAPI.statedScalars_eq_center]
    refine hcent _ (hHY h.2) fun k hk => ?_
    have hcomm : φ h * φ ⟨k, hk⟩ = φ ⟨k, hk⟩ * φ h :=
      ((Subgroup.mem_centralizer_iff.1 hc) _ (hφH _)).symm
    have hker : h * ⟨k, hk⟩ * h⁻¹ * ⟨k, hk⟩⁻¹ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
      group
    have := hφk hker
    rwa [Subgroup.mem_subgroupOf] at this
  · intro hh
    refine ⟨hφH h, Subgroup.mem_centralizer_iff.2 ?_⟩
    rintro _ hs
    rw [← hφS] at hs
    obtain ⟨k, rfl⟩ := hs
    have hz : (h : GL (Fin n) K) ∈ Subgroup.center (GL (Fin n) K) := by
      rw [← CFSG.Open.StatedAPI.statedScalars_eq_center]
      exact Subgroup.mem_subgroupOf.1 hh
    have hhk : k * h = h * k := Subtype.ext (Subgroup.mem_center_iff.1 hz k)
    rw [← map_mul, ← map_mul, hhk]

private theorem inv_mul_mem_centralizer_of_barMk_eq {a b : Ω}
    (h : barMk S a = barMk S b) : a⁻¹ * b ∈ Subgroup.centralizer (S : Set Ω) :=
  (QuotientGroup.eq.1 h).2

theorem actsAs_of_barCover (hH : commutator ↥H = ⊤) (hφS : φ.range = S) {x : Ω}
    {A : GL (Fin n) K} (hA : A ∈ Subgroup.normalizer (H : Set (GL (Fin n) K)))
    (h : ActsAs ((barMk S).comp φ) (barMk S x) A) : ActsAs φ x A := by
  have hφH : ∀ k : ↥H, φ k ∈ S := fun k => hφS ▸ ⟨k, rfl⟩
  have hfeq := eq_of_inv_mul_mem_centralizer (S := S) hH ((MulAut.conj x).toMonoidHom.comp φ)
    (φ.comp (conjOn hA).toMonoidHom) (fun k => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact (inferInstance : S.Normal).conj_mem _ (hφH k) x)
    (fun k => hφH _) (fun k => by
      obtain ⟨k', hk', hφ⟩ := h k
      have hkk : k' = conjOn hA k := Subtype.ext (by rw [hk', coe_conjOn])
      apply inv_mul_mem_centralizer_of_barMk_eq
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hkk]
      rw [map_mul, map_mul, map_inv]
      exact hφ.symm)
  intro k
  refine ⟨conjOn hA k, coe_conjOn hA k, ?_⟩
  have := congrArg (fun f => f k) hfeq
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  exact this.symm

theorem fieldAct_of_barCover (hH : commutator ↥H = ⊤) (hφS : φ.range = S) {p : ℕ} {b : Ω}
    {A : GL (Fin n) K} {σ : K ≃+* K} (h : FieldAct p ((barMk S).comp φ) (barMk S b) A σ) :
    FieldAct p φ b A σ := by
  obtain ⟨hσ, hcard, hact⟩ := h
  refine ⟨hσ, hcard, ?_⟩
  have hφH : ∀ k : ↥H, φ k ∈ S := fun k => hφS ▸ ⟨k, rfl⟩
  have hsH : ∀ k : ↥H, semiConj A σ k ∈ H := fun k => by
    obtain ⟨k', hk', -⟩ := hact k
    rw [← hk']
    exact k'.2
  set τ : ↥H →* ↥H := ((semiConj A σ).toMonoidHom.comp H.subtype).codRestrict H hsH with hτ
  have hfeq := eq_of_inv_mul_mem_centralizer (S := S) hH ((MulAut.conj b).toMonoidHom.comp φ)
    (φ.comp τ) (fun k => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact (inferInstance : S.Normal).conj_mem _ (hφH k) b)
    (fun k => hφH _) (fun k => by
      obtain ⟨k', hk', hφ⟩ := hact k
      have hkk : k' = τ k := Subtype.ext hk'
      apply inv_mul_mem_centralizer_of_barMk_eq
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hkk]
      rw [map_mul, map_mul, map_inv]
      exact hφ.symm)
  intro k
  refine ⟨τ k, rfl, ?_⟩
  have := congrArg (fun f => f k) hfeq
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  exact this.symm

end Bar

section Comm

theorem semiConj_mul_inv_mem_center [Finite ↥H] {φ : ↥H →* Ω} {Y : Subgroup (GL (Fin n) K)}
    (hYN : Y ≤ Subgroup.normalizer (H : Set (GL (Fin n) K)))
    (hcent : ∀ c ∈ Y, (∀ k ∈ H, c * k * c⁻¹ * k⁻¹ ∈ StatedScalars (Fin n) K) →
      c ∈ Subgroup.center (GL (Fin n) K))
    (hφk : φ.ker ≤ (StatedScalars (Fin n) K).subgroupOf H) {p : ℕ} {b x : Ω}
    {A A' : GL (Fin n) K} {σ : K ≃+* K} (hb : FieldAct p φ b A σ) (hA' : A' ∈ Y)
    (hsA' : semiConj A σ A' ∈ Y) (hx : ActsAs φ x A') (hbx : b * x = x * b) :
    semiConj A σ A' * A'⁻¹ ∈ Subgroup.center (GL (Fin n) K) := by
  have hsH := Cls.semiConj_mem_of_fieldAct hb
  have hmap := Cls.map_semiConj_eq hsH
  have hact : ActsAs φ x (semiConj A σ A') := by
    intro k
    obtain ⟨k₁, hk₁H, hk₁⟩ : (k : GL (Fin n) K) ∈ H.map (semiConj A σ : GL (Fin n) K →* _) :=
      hmap.symm ▸ k.2
    obtain ⟨k₂, hk₂, hφ₂⟩ := hx ⟨k₁, hk₁H⟩
    obtain ⟨k', hk', hφ'⟩ := hb.2.2 k₂
    obtain ⟨k₀, hk₀, hφ₀⟩ := hb.2.2 ⟨k₁, hk₁H⟩
    have hk₀k : k₀ = k := Subtype.ext (by rw [hk₀]; exact hk₁)
    refine ⟨k', ?_, ?_⟩
    · rw [hk', hk₂, map_mul, map_mul, map_inv]
      congr 2
    · rw [hφ', hφ₂, ← hk₀k, hφ₀]
      calc b * (x * φ ⟨k₁, hk₁H⟩ * x⁻¹) * b⁻¹
          = (b * x) * φ ⟨k₁, hk₁H⟩ * (b * x)⁻¹ := by group
        _ = (x * b) * φ ⟨k₁, hk₁H⟩ * (x * b)⁻¹ := by rw [hbx]
        _ = x * (b * φ ⟨k₁, hk₁H⟩ * b⁻¹) * x⁻¹ := by group
  have h1 := inv_mul_mem_center_of_actsAs hYN hcent hφk hA' hsA' hx hact
  have h2 : semiConj A σ A' * A'⁻¹ = A' * (A'⁻¹ * semiConj A σ A') * A'⁻¹ := by group
  rw [h2, Subgroup.mem_center_iff.1 h1 A', mul_inv_cancel_right]
  exact h1

end Comm

section Torus

open CFSG.HardMathSupport.Timmesfeld.ComponentBalance in
theorem le_glaTwoLocalRank_of_torus [Finite Ω] [S.Normal] {p : ℕ} (hp : p.Prime) {φ : ↥H →* Ω}
    (hφS : φ.range = S) (hφZ : ((barMk S).comp φ).ker = (StatedScalars (Fin n) K).subgroupOf H)
    {X : Subgroup (GL (Fin n) K)} (hXH : X ≤ H) (hX : IsElemAbelian p X)
    (hXZ : X ⊓ StatedScalars (Fin n) K = ⊥) {r : ℕ} (hXc : Nat.card X = p ^ r)
    {t : GL (Fin n) K} (htH : t ∈ H) (ht2 : t ^ 2 = 1) (htZ : t ∉ StatedScalars (Fin n) K)
    (hXt : ∀ x ∈ X, x * t = t * x) {B₂ : Subgroup Ω} (hB₂ : IsElemAbelian p B₂) {s : ℕ}
    (hB₂c : Nat.card B₂ = p ^ s) (hB₂S : B₂ ⊓ S ≤ Subgroup.centralizer (S : Set Ω))
    (hB₂X : ∀ y ∈ B₂, ∀ x : ↥H, (x : GL (Fin n) K) ∈ X → y * φ x = φ x * y)
    (hB₂t : ∀ y ∈ B₂, y * φ ⟨t, htH⟩ = φ ⟨t, htH⟩ * y) :
    r + s ≤ GLATwoLocalRank p Ω := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hφH : ∀ k : ↥H, φ k ∈ S := fun k => hφS ▸ ⟨k, rfl⟩
  have hker : ∀ k : ↥H, φ k = 1 → (k : GL (Fin n) K) ∈ StatedScalars (Fin n) K := fun k hk => by
    have : k ∈ ((barMk S).comp φ).ker := by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hk, map_one]
    rw [hφZ, Subgroup.mem_subgroupOf] at this
    exact this
  have hcen : ∀ k : ↥H, φ k ∈ Subgroup.centralizer (S : Set Ω) →
      (k : GL (Fin n) K) ∈ StatedScalars (Fin n) K := fun k hk => by
    have : k ∈ ((barMk S).comp φ).ker := by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      exact ⟨hφH k, hk⟩
    rw [hφZ, Subgroup.mem_subgroupOf] at this
    exact this
  set φX : ↥(X.subgroupOf H) →* Ω := φ.comp (X.subgroupOf H).subtype with hφX
  have hφXinj : Function.Injective φX := by
    intro a a' heq
    have h1 : φ ((a : ↥H)⁻¹ * a') = 1 := by
      have : φX a = φX a' := heq
      simp only [hφX, MonoidHom.comp_apply, Subgroup.coe_subtype] at this
      rw [map_mul, map_inv, this, inv_mul_cancel]
    have h2 := hker _ h1
    have h3 : (((a : ↥H)⁻¹ * a' : ↥H) : GL (Fin n) K) ∈ X ⊓ StatedScalars (Fin n) K :=
      ⟨X.mul_mem (X.inv_mem a.2) a'.2, h2⟩
    rw [hXZ, Subgroup.mem_bot] at h3
    exact Subtype.ext (inv_mul_eq_one.1 (Subtype.ext h3))
  set Xb : Subgroup Ω := φX.range with hXb
  have hXbc : Nat.card Xb = p ^ r := by
    rw [hXb, ← Nat.card_congr (MonoidHom.ofInjective hφXinj).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv, hXc]
  have hXbS : Xb ≤ S := by
    rintro _ ⟨a, rfl⟩
    exact hφH _
  have hXbel : IsElemAbelian p Xb := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, x, rfl⟩ := a
      obtain ⟨_, y, rfl⟩ := b
      apply Subtype.ext
      show φX x * φX y = φX y * φX x
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : ↥X => (z : GL (Fin n) K)) (hX.1.is_comm.comm ⟨_, x.2⟩ ⟨_, y.2⟩)
    · rintro _ ⟨x, rfl⟩
      rw [← map_pow]
      have : x ^ p = 1 := Subtype.ext (Subtype.ext (hX.2 _ x.2))
      rw [this, map_one]
  have hcomm : ∀ y ∈ B₂, ∀ z ∈ Xb, y * z = z * y := by
    rintro y hy _ ⟨x, rfl⟩
    exact hB₂X y hy x x.2
  have hinf : B₂ ⊓ Xb = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨hy, ⟨x, rfl⟩⟩
    have hc : φX x ∈ Subgroup.centralizer (S : Set Ω) := hB₂S ⟨hy, hXbS ⟨x, rfl⟩⟩
    have h1 := hcen _ hc
    have h2 : ((x : ↥H) : GL (Fin n) K) ∈ X ⊓ StatedScalars (Fin n) K := ⟨x.2, h1⟩
    rw [hXZ, Subgroup.mem_bot] at h2
    have hx1 : x = 1 := Subtype.ext (Subtype.ext h2)
    rw [Subgroup.mem_bot, hx1, map_one]
  have hPel : IsElemAbelian p (B₂ ⊔ Xb) := IsElemAbelian.sup_of_commute hB₂ hXbel hcomm
  have hPc : Nat.card ↥(B₂ ⊔ Xb) = p ^ (r + s) := by
    rw [GL83.CompFam.card_sup_of_commute_of_inf_eq_bot hcomm hinf, hB₂c, hXbc, ← pow_add,
      add_comm]
  set u := φ ⟨t, htH⟩ with hu
  have hu1 : u ≠ 1 := fun h => htZ (hker _ h)
  have hu2 : u ^ 2 = 1 := by
    rw [hu, ← map_pow]
    have : (⟨t, htH⟩ : ↥H) ^ 2 = 1 := Subtype.ext ht2
    rw [this, map_one]
  have hT : Subgroup.zpowers u ≠ ⊥ := fun h => hu1 (Subgroup.zpowers_eq_bot.1 h)
  have hT2 : IsPGroup 2 (Subgroup.zpowers u) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime hu2 hu1
  have hPN : B₂ ⊔ Xb ≤ Subgroup.normalizer (Subgroup.zpowers u : Set Ω) := by
    have hcu : ∀ g, g * u = u * g → g ∈ Subgroup.normalizer (Subgroup.zpowers u : Set Ω) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have hcomm' : ∀ h ∈ Subgroup.zpowers u, g * h * g⁻¹ = h := by
        rintro _ ⟨k, rfl⟩
        have : Commute g (u ^ k) := (show Commute g u from hg).zpow_right k
        simp only
        rw [this.eq, mul_inv_cancel_right]
      constructor
      · intro hh
        rw [hcomm' h hh]
        exact hh
      · intro hh
        have h1 : h = g⁻¹ * (g * h * g⁻¹) * g := by group
        rw [h1]
        have hgi : g⁻¹ * u = u * g⁻¹ := by
          calc g⁻¹ * u = g⁻¹ * (u * g) * g⁻¹ := by group
            _ = g⁻¹ * (g * u) * g⁻¹ := by rw [hg]
            _ = u * g⁻¹ := by group
        obtain ⟨k, hk⟩ := hh
        rw [← hk]
        have : Commute g⁻¹ (u ^ k) := (show Commute g⁻¹ u from hgi).zpow_right k
        rw [this.eq, inv_mul_cancel_right]
        exact Subgroup.zpow_mem_zpowers u k
    refine sup_le (fun y hy => hcu y (hB₂t y hy)) ?_
    rintro _ ⟨x, rfl⟩
    refine hcu _ ?_
    show φ x * φ ⟨t, htH⟩ = φ ⟨t, htH⟩ * φ x
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hXt _ x.2)
  exact le_glaTwoLocalRank_of_le_normalizer hp.one_lt hT hT2 hPel hPN hPc

end Torus

section Diagonal

open CFSG.SectionRank.OddCover

theorem ringEquiv_apply_eq_self_of_pow_eq_one {L : Type*} [Field L] {p : ℕ} (hp : p.Prime)
    {σ : L ≃+* L} (hσ : σ ^ p = 1) {ζ : L} (hζ : ζ ^ p = 1) : σ ζ = ζ := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases h1 : ζ = 1
  · rw [h1, map_one]
  have hord : orderOf ζ = p := orderOf_eq_prime hζ h1
  have hprim : IsPrimitiveRoot ζ p := IsPrimitiveRoot.iff_orderOf.2 hord
  obtain ⟨k, hkp, hk⟩ := hprim.eq_pow_of_pow_eq_one
    (show (σ ζ) ^ p = 1 by rw [← map_pow, hζ, map_one])
  have hit : ∀ j : ℕ, (σ ^ j) ζ = ζ ^ (k ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', RingAut.mul_apply, ih, map_pow, ← hk, ← pow_mul, pow_succ']
  have h2 : ζ ^ (k ^ p % p) = ζ ^ 1 := by
    rw [← hord, pow_mod_orderOf, hord, ← hit p, hσ, pow_one]
    rfl
  have h3 : k ^ p % p = 1 :=
    hprim.pow_inj (Nat.mod_lt _ hp.pos) hp.one_lt h2
  have h4 : ((k : ℕ) : ZMod p) = 1 := by
    rw [← ZMod.pow_card ((k : ℕ) : ZMod p), ← Nat.cast_pow, ← ZMod.natCast_mod, h3, Nat.cast_one]
  have h5 : k = 1 := by
    have := (ZMod.natCast_eq_natCast_iff' k 1 p).1 (by rw [h4, Nat.cast_one])
    rwa [Nat.mod_eq_of_lt hkp, Nat.mod_eq_of_lt hp.one_lt] at this
  rw [← hk, h5, pow_one]

variable {L : Type} [Field L]

@[expose] noncomputable def torusVec (m p : ℕ) (L : Type) [Field L] :
    (Fin m → ↥(rootsOfUnity p L)) →* (Fin (m + 2) → Lˣ) where
  toFun e i := if h : (i : ℕ) < m then (e ⟨i, h⟩ : Lˣ)
    else if (i : ℕ) = m then (∏ j, (e j : Lˣ))⁻¹ else 1
  map_one' := by
    funext i
    simp only [Pi.one_apply, OneMemClass.coe_one, Finset.prod_const_one, inv_one]
    split_ifs <;> rfl
  map_mul' e e' := by
    funext i
    simp only [Pi.mul_apply, Subgroup.coe_mul, Finset.prod_mul_distrib, mul_inv]
    split_ifs <;> simp

@[expose] noncomputable def diagTorus (m p : ℕ) (L : Type) [Field L] :
    Subgroup (GL (Fin (m + 2)) L) :=
  ((diagHom (m + 2)).comp (torusVec m p L)).range

@[expose] noncomputable def diagInvol (m : ℕ) (L : Type) [Field L] : GL (Fin (m + 2)) L :=
  diagHom (m + 2) fun i => if (i : ℕ) < 2 then -1 else 1

theorem torusVec_injective (m p : ℕ) : Function.Injective (torusVec m p L) := by
  intro e e' h
  funext j
  have := congrFun h ⟨j, by omega⟩
  simp only [torusVec, MonoidHom.coe_mk, OneHom.coe_mk, j.isLt, dite_true] at this
  exact Subtype.ext this

theorem card_diagTorus [Finite L] {p : ℕ} (hp : p.Prime) (hpL : p ∣ Nat.card Lˣ) (m : ℕ) :
    Nat.card (diagTorus m p L) = p ^ m := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' p hpL
  have hprim : IsPrimitiveRoot (ζ : L) p :=
    IsPrimitiveRoot.coe_units_iff.2 (IsPrimitiveRoot.iff_orderOf.2 hζ)
  have hinj : Function.Injective ((diagHom (m + 2)).comp (torusVec m p L)) :=
    (diagHom_injective (m + 2)).comp (torusVec_injective m p)
  rw [diagTorus, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_fun,
    hprim.card_rootsOfUnity, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem torusVec_pow (m p : ℕ) (e : Fin m → ↥(rootsOfUnity p L)) (i : Fin (m + 2)) :
    torusVec m p L e i ^ p = 1 := by
  simp only [torusVec, MonoidHom.coe_mk, OneHom.coe_mk]
  split_ifs
  · exact (mem_rootsOfUnity p _).1 (e _).2
  · rw [inv_pow, ← Finset.prod_pow, Finset.prod_eq_one fun j _ => (mem_rootsOfUnity p _).1 (e j).2,
      inv_one]
  · exact one_pow p

theorem torusVec_prod (m p : ℕ) (e : Fin m → ↥(rootsOfUnity p L)) :
    ∏ i, torusVec m p L e i = 1 := by
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
  simp only [torusVec, MonoidHom.coe_mk, OneHom.coe_mk, Fin.coe_castSucc, Fin.val_last]
  have h1 : ∀ i : Fin m, ((i : ℕ) : ℕ) < m := fun i => i.isLt
  simp only [Fin.is_lt, dite_true, lt_irrefl, dite_false, if_true, show ¬ (m + 1 < m) by omega,
    show m + 1 ≠ m by omega, if_false, mul_one]
  rw [mul_inv_cancel]

theorem diagTorus_le_det_one {m p : ℕ} {x : GL (Fin (m + 2)) L} (hx : x ∈ diagTorus m p L) :
    (x : Matrix (Fin (m + 2)) (Fin (m + 2)) L).det = 1 := by
  obtain ⟨e, rfl⟩ := hx
  rw [MonoidHom.comp_apply, coe_diagHom, Matrix.det_diagonal]
  rw [← Units.val_one, ← torusVec_prod m p e]
  simp

theorem diagTorus_map_eq {m p : ℕ} (hp : p.Prime) {σ : L ≃+* L} (hσ : σ ^ p = 1)
    {x : GL (Fin (m + 2)) L} (hx : x ∈ diagTorus m p L) :
    (x : Matrix (Fin (m + 2)) (Fin (m + 2)) L).map σ = x := by
  obtain ⟨e, rfl⟩ := hx
  rw [MonoidHom.comp_apply, coe_diagHom, Matrix.diagonal_map (map_zero σ)]
  congr 1
  funext i
  exact ringEquiv_apply_eq_self_of_pow_eq_one hp hσ
    (by rw [← Units.val_pow_eq_pow_val, torusVec_pow, Units.val_one])

theorem diagInvol_map_eq (m : ℕ) (σ : L ≃+* L) :
    ((diagInvol m L : GL (Fin (m + 2)) L) : Matrix (Fin (m + 2)) (Fin (m + 2)) L).map σ =
      diagInvol m L := by
  rw [diagInvol, coe_diagHom, Matrix.diagonal_map (map_zero σ)]
  congr 1
  funext i
  split_ifs <;> simp

theorem diagInvol_sq (m : ℕ) : diagInvol m L ^ 2 = 1 := by
  rw [diagInvol, ← map_pow, ← map_one (diagHom (K := L) (m + 2))]
  congr 1
  funext i
  simp only [Pi.pow_apply, Pi.one_apply]
  split_ifs <;> simp

theorem diagInvol_det (m : ℕ) :
    ((diagInvol m L : GL (Fin (m + 2)) L) : Matrix (Fin (m + 2)) (Fin (m + 2)) L).det = 1 := by
  rw [diagInvol, coe_diagHom, Matrix.det_diagonal, Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, Fin.succ_zero_eq_one, Fin.val_one]
  have h : ∀ i : Fin m, ¬ ((i.succ.succ : Fin (m + 2)) : ℕ) < 2 := fun i => by
    simp [Fin.val_succ]
  simp [h]

theorem diagInvol_not_mem (m : ℕ) (h2 : (2 : L) ≠ 0) (hm : 1 ≤ m) :
    diagInvol m L ∉ Subgroup.center (GL (Fin (m + 2)) L) := by
  intro hc
  obtain ⟨c, hc⟩ := mem_center_iff.1 hc
  have h0 := congrArg (fun g : GL (Fin (m + 2)) L => (g : Matrix (Fin (m + 2)) (Fin (m + 2)) L)
    ⟨0, by omega⟩ ⟨0, by omega⟩) hc
  have h1 := congrArg (fun g : GL (Fin (m + 2)) L => (g : Matrix (Fin (m + 2)) (Fin (m + 2)) L)
    ⟨2, by omega⟩ ⟨2, by omega⟩) hc
  simp [diagInvol, coe_diagHom, GeneralLinearGroup.coe_scalar] at h0 h1
  apply h2
  have : (-1 : L) = 1 := h0.trans h1.symm
  linear_combination -this

theorem diagTorus_comm_diagInvol {m p : ℕ} {x : GL (Fin (m + 2)) L} (hx : x ∈ diagTorus m p L) :
    x * diagInvol m L = diagInvol m L * x := by
  obtain ⟨e, rfl⟩ := hx
  rw [MonoidHom.comp_apply, diagInvol, ← map_mul, ← map_mul, mul_comm]

theorem diagTorus_inf_center {m p : ℕ} :
    diagTorus m p L ⊓ Subgroup.center (GL (Fin (m + 2)) L) = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨⟨e, rfl⟩, hc⟩
  obtain ⟨c, hc⟩ := mem_center_iff.1 hc
  rw [Subgroup.mem_bot]
  have hlast := congrArg (fun g : GL (Fin (m + 2)) L => (g : Matrix (Fin (m + 2)) (Fin (m + 2)) L)
    (Fin.last (m + 1)) (Fin.last (m + 1))) hc
  simp only [MonoidHom.comp_apply, coe_diagHom, Matrix.diagonal_apply_eq,
    GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at hlast
  simp only [torusVec, MonoidHom.coe_mk, OneHom.coe_mk, Fin.val_last,
    show ¬ (m + 1 < m) by omega, show m + 1 ≠ m by omega, dite_false, if_false,
    Units.val_one] at hlast
  have hc1 : c = 1 := Units.ext hlast.symm
  rw [hc, hc1, map_one]

theorem isElemAbelian_diagTorus (m p : ℕ) : IsElemAbelian p (diagTorus m p L) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨_, e, rfl⟩ := a
    obtain ⟨_, e', rfl⟩ := b
    exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, ← map_mul, ← map_mul, mul_comm])
  · rintro _ ⟨e, rfl⟩
    rw [← map_pow]
    have : e ^ p = 1 := funext fun j => Subtype.ext ((mem_rootsOfUnity p _).1 (e j).2)
    rw [this, map_one]

end Diagonal

end CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

end
