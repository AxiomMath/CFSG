module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78L2Coord
public import CFSG.LocalAnalysis.ComponentClassification.GMS78BasicLinear

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open
open CFSG.ComponentClassification.AschbacherToolkit.Bender
open CFSG.ComponentClassification.AschbacherToolkit.Bender.LinearInv
open scoped MatrixGroups

variable {f : ℕ}

theorem sl2Data (hf : 2 ≤ f) :
    IsSimpleGroup SL(2, GaloisField 2 f) ∧ ∃ U V : Sylow 2 SL(2, GaloisField 2 f),
      (U : Subgroup SL(2, GaloisField 2 f)) = upSub ∧
      (V : Subgroup SL(2, GaloisField 2 f)) = loSub ∧
      fusionStronglyEmbedded
        (normalizer ((U : Subgroup SL(2, GaloisField 2 f)) : Set SL(2, GaloisField 2 f))) ∧
      Nat.card (Sylow 2 SL(2, GaloisField 2 f)) =
        Nat.card (U : Subgroup SL(2, GaloisField 2 f)) + 1 := by
  classical
  set K := GaloisField 2 f
  have : Finite K := inferInstance
  let eS : PSL(2, K) ≃* SL(2, K) := CFSG.Walter.psl2MulEquivSL2OfCharTwo
  have : Finite PSL(2, K) := Finite.of_injective eS eS.injective
  have hB : fusionBenderBorel SL(2, K) (2 ^ f) 1 :=
    (CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_1 f
      hf).map_mulEquiv eS
  have hsimple : IsSimpleGroup SL(2, K) :=
    CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup
      (Or.inl ⟨f, hf, ⟨eS.symm⟩⟩)
  have hKcard : Nat.card K = 2 ^ f := GaloisField.card 2 f (by omega)
  have hsyl : ∀ H : Subgroup SL(2, K), Nat.card H = 2 ^ f →
      ∃ P : Sylow 2 SL(2, K), (P : Subgroup SL(2, K)) = H := by
    intro H hH
    obtain ⟨P, hP⟩ := (IsPGroup.of_card hH).exists_le_sylow
    refine ⟨P, (Subgroup.eq_of_le_of_card_ge hP ?_).symm⟩
    obtain ⟨-, -, -, hPcard⟩ := benderBorel_sylowCenter hB P
    rw [hPcard, hH, pow_one]
  obtain ⟨U, hU⟩ := hsyl upSub (by rw [card_upSub, hKcard])
  obtain ⟨V, hV⟩ := hsyl loSub (by rw [card_loSub, hKcard])
  obtain ⟨hSE, -, -, hUcard⟩ := benderBorel_sylowCenter hB U
  refine ⟨hsimple, U, V, hU, hV, hSE, ?_⟩
  rw [← card_sylow_eq_of_mulEquiv eS 2, CFSG.Walter.psl2_even_card_sylow (by omega), hUcard,
    pow_one]

section Twist

variable {K : Type*} [Field K] [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem exists_twist {U V : Sylow 2 SL(2, K)}
    (hSE : fusionStronglyEmbedded (normalizer ((U : Subgroup SL(2, K)) : Set SL(2, K))))
    (hcard : Nat.card (Sylow 2 SL(2, K)) = Nat.card (U : Subgroup SL(2, K)) + 1) (hVU : V ≠ U)
    {γ : MulAut SL(2, K)} {R : Sylow 2 SL(2, K)} (hγR : γ • R = R) {g : SL(2, K)}
    (hg : g • R = U) : ∃ r ∈ (U : Subgroup SL(2, K)),
      ((MulAut.conj r)⁻¹ * (MulAut.conj g * γ * (MulAut.conj g)⁻¹)) • U = U ∧
      ((MulAut.conj r)⁻¹ * (MulAut.conj g * γ * (MulAut.conj g)⁻¹)) • V = V := by
  set γ₁ := MulAut.conj g * γ * (MulAut.conj g)⁻¹ with hγ₁
  have h1 : γ₁ • U = U := by
    rw [hγ₁, ← hg, Sylow.smul_def, mul_smul, mul_smul, inv_smul_smul, hγR]
  have h2 : γ₁ • V ≠ U := by
    intro h
    apply hVU
    have h' : γ₁ • V = γ₁ • U := h.trans h1.symm
    exact smul_left_cancel γ₁ h'
  obtain ⟨r, hrU, hr⟩ := Omega.exists_smul_eq hSE hcard hVU h2
  refine ⟨r, hrU, ?_, ?_⟩
  · rw [mul_smul, h1, inv_smul_eq_iff, eq_comm, RankTwoBender.conj_smul_eq_iff]
    exact le_normalizer hrU
  · rw [mul_smul, ← hr, Sylow.smul_def, inv_smul_smul]

omit [Finite K] [CharP K 2] in
theorem twist_eq (γ : MulAut SL(2, K)) (g r : SL(2, K)) :
    (MulAut.conj r)⁻¹ * (MulAut.conj g * γ * (MulAut.conj g)⁻¹) =
      MulAut.conj (r⁻¹ * g) * γ * MulAut.conj g⁻¹ := by
  rw [map_mul, map_inv, map_inv]
  group

omit [Finite K] [CharP K 2] in
theorem inner_of_twist {γ : MulAut SL(2, K)} {g r y : SL(2, K)}
    (hy : (MulAut.conj r)⁻¹ * (MulAut.conj g * γ * (MulAut.conj g)⁻¹) = MulAut.conj y) :
    ∃ z, γ = MulAut.conj z := by
  refine ⟨g⁻¹ * r * y * g, ?_⟩
  calc γ = (MulAut.conj g)⁻¹ * MulAut.conj r *
        ((MulAut.conj r)⁻¹ * (MulAut.conj g * γ * (MulAut.conj g)⁻¹)) * MulAut.conj g := by
        group
    _ = MulAut.conj (g⁻¹ * r * y * g) := by rw [hy, map_mul, map_mul, map_mul, map_inv]

omit [Finite K] [CharP K 2] in
theorem sq_twist {γ : MulAut SL(2, K)} (hγγ : ∃ y, γ * γ = MulAut.conj y) (g r : SL(2, K)) :
    ∃ z, ((MulAut.conj r)⁻¹ * (MulAut.conj g * γ * (MulAut.conj g)⁻¹)) *
      ((MulAut.conj r)⁻¹ * (MulAut.conj g * γ * (MulAut.conj g)⁻¹)) = MulAut.conj z := by
  obtain ⟨y, hy⟩ := hγγ
  rw [twist_eq]
  exact ⟨_, sq_conj_mul_conj hy _ _⟩

end Twist

theorem twist_coord (hf : 2 ≤ f) {U V : Sylow 2 SL(2, GaloisField 2 f)}
    (hU : (U : Subgroup SL(2, GaloisField 2 f)) = upSub)
    (hV : (V : Subgroup SL(2, GaloisField 2 f)) = loSub)
    (hSE : fusionStronglyEmbedded
      (normalizer ((U : Subgroup SL(2, GaloisField 2 f)) : Set SL(2, GaloisField 2 f))))
    (hcard : Nat.card (Sylow 2 SL(2, GaloisField 2 f)) =
      Nat.card (U : Subgroup SL(2, GaloisField 2 f)) + 1)
    {γ : MulAut SL(2, GaloisField 2 f)} (hγγ : ∃ y, γ * γ = MulAut.conj y)
    (hγ : ¬ ∃ y, γ = MulAut.conj y) (g r : SL(2, GaloisField 2 f))
    (h1 : ((MulAut.conj r)⁻¹ * (MulAut.conj g * γ * (MulAut.conj g)⁻¹)) • U = U)
    (h2 : ((MulAut.conj r)⁻¹ * (MulAut.conj g * γ * (MulAut.conj g)⁻¹)) • V = V) :
    ∃ (θ : GaloisField 2 f →+* GaloisField 2 f) (lam : GaloisField 2 f), lam ≠ 0 ∧
      (∃ e, θ e ≠ e) ∧ (∀ b, θ (θ b) = b) ∧
      ∀ b, ((MulAut.conj r)⁻¹ * (MulAut.conj g * γ * (MulAut.conj g)⁻¹)) (up b) =
        up (lam * θ b) := by
  obtain ⟨hsimple, -⟩ := sl2Data hf
  set γ' := (MulAut.conj r)⁻¹ * (MulAut.conj g * γ * (MulAut.conj g)⁻¹) with hγ'
  obtain ⟨θ, lam, hlam0, hγ'up⟩ := coord_of_fix U V hU hV γ' h1 h2
  have hθθ := involutive_of_sq_inner U V hU hV γ' h1 h2 hγ'up (sq_twist hγγ g r)
  refine ⟨θ, lam, hlam0, ?_, hθθ, hγ'up⟩
  by_contra hall
  push Not at hall
  obtain ⟨y, hy⟩ := inner_of_coord_id U V hU hV hSE hcard γ' h1 h2 hlam0
    (fun b => by rw [hγ'up, hall])
  exact hγ (inner_of_twist hy)

theorem inner_of_sq_inner_of_odd_sl2 (hf : 2 ≤ f) (hodd : Odd f)
    (γ : MulAut SL(2, GaloisField 2 f)) (hγγ : ∃ y, γ * γ = MulAut.conj y)
    (R : Sylow 2 SL(2, GaloisField 2 f))
    (hγR : ∀ r ∈ (R : Subgroup SL(2, GaloisField 2 f)), γ r ∈ (R : Subgroup _)) :
    ∃ y, γ = MulAut.conj y := by
  classical
  by_contra hγ
  set K := GaloisField 2 f
  obtain ⟨hsimple, U, V, hU, hV, hSE, hcard⟩ := sl2Data hf
  have hVU : V ≠ U := by
    intro h
    apply upSub_ne_loSub (K := K)
    rw [← hU, ← hV, h]
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(2, K) R U
  obtain ⟨r, -, h1, h2⟩ := exists_twist hSE hcard hVU (Omega.smul_eq_of_mapsTo hγR) hg
  obtain ⟨θ, -, -, ⟨e₀, he₀⟩, hθθ, -⟩ := twist_coord hf hU hV hSE hcard hγγ hγ g r h1 h2
  have hfix := InvField.card_fix_sq θ hθθ he₀
  rw [GaloisField.card 2 f (by omega)] at hfix
  set n := Nat.card {x : K // θ x = x}
  have hn : n ∣ 2 ^ f := ⟨n, by rw [← hfix, sq]⟩
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hn
  rw [hk, ← pow_mul] at hfix
  have := Nat.pow_right_injective (le_refl 2) hfix
  obtain ⟨m, hm⟩ := hodd
  omega

theorem card_fix_sq_le_of_sq_inner_sl2 (hf : 2 ≤ f)
    (γ : MulAut SL(2, GaloisField 2 f)) (hγγ : ∃ y, γ * γ = MulAut.conj y)
    (hγ : ¬ ∃ y, γ = MulAut.conj y) (R : Sylow 2 SL(2, GaloisField 2 f))
    (hγR : ∀ r ∈ (R : Subgroup SL(2, GaloisField 2 f)), γ r ∈ (R : Subgroup _)) :
    Nat.card {r : (R : Subgroup SL(2, GaloisField 2 f)) // γ r = r} ^ 2 ≤
      Nat.card (R : Subgroup SL(2, GaloisField 2 f)) := by
  classical
  set K := GaloisField 2 f
  obtain ⟨hsimple, U, V, hU, hV, hSE, hcard⟩ := sl2Data hf
  have hVU : V ≠ U := by
    intro h
    apply upSub_ne_loSub (K := K)
    rw [← hU, ← hV, h]
  have hγR' : γ • R = R := Omega.smul_eq_of_mapsTo hγR
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(2, K) R U
  obtain ⟨r, hrU, h1, h2⟩ := exists_twist hSE hcard hVU hγR' hg
  obtain ⟨θ, lam, -, ⟨e₀, he₀⟩, hθθ, hγ'up⟩ := twist_coord hf hU hV hSE hcard hγγ hγ g r h1 h2
  have hfix := InvField.card_fix_sq θ hθθ he₀
  have hmemU : ∀ y : SL(2, K),
      y ∈ (R : Subgroup SL(2, K)) ↔ g * y * g⁻¹ ∈ (U : Subgroup SL(2, K)) := by
    intro y
    rw [← hg, Omega.mem_conj_smul_iff]
    simp [mul_assoc]
  have hex : ∀ y : {y : (R : Subgroup SL(2, K)) // γ y = y}, ∃ b : K,
      g * (y.1 : SL(2, K)) * g⁻¹ = up b ∧ lam * θ b = b := by
    rintro ⟨⟨y, hyR⟩, hy⟩
    have hyU := (hmemU y).mp hyR
    rw [hU] at hyU
    obtain ⟨b, hb⟩ := mem_upSub.mp hyU
    refine ⟨b, hb, up_injective ?_⟩
    rw [← hγ'up, ← hb]
    have hy' : γ y = y := hy
    have hrU' : r ∈ upSub := hU ▸ hrU
    obtain ⟨c, rfl⟩ := mem_upSub.mp hrU'
    simp only [MulAut.mul_apply, MulAut.inv_apply, MulAut.conj_symm_apply, MulAut.conj_apply]
    have h3 : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rw [h3, hy', hb, up_inv, up_mul, up_mul]
    congr 1
    ring
  choose bOf hbOf using hex
  have hinj : Function.Injective (fun y => (⟨bOf y, (hbOf y).2⟩ : {b : K // lam * θ b = b})) := by
    intro y y' hyy
    have h1 : bOf y = bOf y' := congrArg Subtype.val hyy
    have h2 : g * (y.1 : SL(2, K)) * g⁻¹ = g * (y'.1 : SL(2, K)) * g⁻¹ := by
      rw [(hbOf y).1, (hbOf y').1, h1]
    exact Subtype.ext (Subtype.ext (by simpa using h2))
  have hle := Nat.card_le_card_of_injective _ hinj
  have hle2 := card_fix_semilinear_le θ lam
  have hRU : Nat.card (R : Subgroup SL(2, K)) = Nat.card (U : Subgroup SL(2, K)) := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  have hRcard : Nat.card (R : Subgroup SL(2, K)) = Nat.card K := by
    rw [hRU, hU, card_upSub]
  calc Nat.card {r : (R : Subgroup SL(2, K)) // γ r = r} ^ 2
      ≤ Nat.card {x : K // θ x = x} ^ 2 := Nat.pow_le_pow_left (hle.trans hle2) 2
    _ = Nat.card (R : Subgroup SL(2, K)) := by rw [hfix, hRcard]

theorem mul_inv_inner_of_sq_inner_sl2 (hf : 2 ≤ f)
    {γ₁ γ₂ : MulAut SL(2, GaloisField 2 f)} (h₁ : ∃ y, γ₁ * γ₁ = MulAut.conj y)
    (h₂ : ∃ y, γ₂ * γ₂ = MulAut.conj y) (hn₁ : ¬ ∃ y, γ₁ = MulAut.conj y)
    (hn₂ : ¬ ∃ y, γ₂ = MulAut.conj y) (R : Sylow 2 SL(2, GaloisField 2 f))
    (hR₁ : ∀ r ∈ (R : Subgroup SL(2, GaloisField 2 f)), γ₁ r ∈ (R : Subgroup _))
    (hR₂ : ∀ r ∈ (R : Subgroup SL(2, GaloisField 2 f)), γ₂ r ∈ (R : Subgroup _)) :
    ∃ y, γ₁ * γ₂⁻¹ = MulAut.conj y := by
  classical
  set K := GaloisField 2 f
  obtain ⟨hsimple, U, V, hU, hV, hSE, hcard⟩ := sl2Data hf
  have hVU : V ≠ U := by
    intro h
    apply upSub_ne_loSub (K := K)
    rw [← hU, ← hV, h]
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(2, K) R U
  obtain ⟨r₁, -, h11, h12⟩ := exists_twist hSE hcard hVU (Omega.smul_eq_of_mapsTo hR₁) hg
  obtain ⟨r₂, -, h21, h22⟩ := exists_twist hSE hcard hVU (Omega.smul_eq_of_mapsTo hR₂) hg
  obtain ⟨θ₁, l₁, hl₁, ⟨e₁, he₁⟩, hθ₁, hγ₁⟩ := twist_coord hf hU hV hSE hcard h₁ hn₁ g r₁ h11 h12
  obtain ⟨θ₂, l₂, hl₂, ⟨e₂, he₂⟩, hθ₂, hγ₂⟩ :=
    twist_coord hf hU hV hSE hcard h₂ hn₂ g r₂ h21 h22
  have h21' := RankTwoBender.eq_of_involutive θ₁ θ₂ hθ₁ hθ₂ he₁ he₂
  set γ₁' := (MulAut.conj r₁)⁻¹ * (MulAut.conj g * γ₁ * (MulAut.conj g)⁻¹) with hγ₁'
  set γ₂' := (MulAut.conj r₂)⁻¹ * (MulAut.conj g * γ₂ * (MulAut.conj g)⁻¹) with hγ₂'
  have hinv : ∀ b, γ₂'⁻¹ (up b) = up (θ₁ (l₂⁻¹ * b)) := by
    intro b
    rw [MulAut.inv_apply, MulEquiv.symm_apply_eq, hγ₂, h21', hθ₁]
    congr 1
    field_simp
  have hU' : (γ₁' * γ₂'⁻¹) • U = U := by
    rw [mul_smul, inv_smul_eq_iff.mpr h21.symm, h11]
  have hV' : (γ₁' * γ₂'⁻¹) • V = V := by
    rw [mul_smul, inv_smul_eq_iff.mpr h22.symm, h12]
  have hl : l₁ * l₂⁻¹ ≠ 0 := mul_ne_zero hl₁ (inv_ne_zero hl₂)
  obtain ⟨y, hy⟩ := inner_of_coord_id U V hU hV hSE hcard (γ₁' * γ₂'⁻¹) hU' hV' hl
    (fun b => by rw [MulAut.mul_apply, hinv, hγ₁, hθ₁, mul_assoc])
  refine ⟨g⁻¹ * r₁ * y * r₂⁻¹ * g, ?_⟩
  calc γ₁ * γ₂⁻¹ = (MulAut.conj g)⁻¹ * MulAut.conj r₁ * (γ₁' * γ₂'⁻¹) *
        (MulAut.conj r₂)⁻¹ * MulAut.conj g := by
        rw [hγ₁', hγ₂']
        group
    _ = MulAut.conj (g⁻¹ * r₁ * y * r₂⁻¹ * g) := by
        rw [hy, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv]

theorem card_fix_sq_le_of_sq_inner_psl2 {X : Type*} [Group X]
    [Finite X] (hf : 2 ≤ f) (e : X ≃* PSL(2, GaloisField 2 f)) (α : MulAut X)
    (hαα : ∃ y, α * α = MulAut.conj y) (hα : ¬ ∃ y, α = MulAut.conj y) (R : Sylow 2 X)
    (hαR : ∀ r ∈ (R : Subgroup X), α r ∈ (R : Subgroup X)) :
    Nat.card {r : (R : Subgroup X) // α r = r} ^ 2 ≤ Nat.card (R : Subgroup X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e' : X ≃* SL(2, GaloisField 2 f) := e.trans CFSG.Walter.psl2MulEquivSL2OfCharTwo
  set γ := MulAut.congr e' α with hγ
  have hγapp : ∀ r, γ r = e' (α (e'.symm r)) := fun r => by
    have h := AschbacherToolkit.Bender.AutTransport.congr_apply' e' α (e'.symm r)
    rwa [MulEquiv.apply_symm_apply] at h
  have hγγ : ∃ y, γ * γ = MulAut.conj y := by
    obtain ⟨y, hy⟩ := hαα
    refine ⟨e' y, ?_⟩
    rw [hγ, ← map_mul, hy, AschbacherToolkit.Bender.AutTransport.congr_conj]
  have hγout : ¬ ∃ y, γ = MulAut.conj y := by
    rintro ⟨y, hy⟩
    apply hα
    refine ⟨e'.symm y, (MulAut.congr e').injective ?_⟩
    rw [AschbacherToolkit.Bender.AutTransport.congr_conj, MulEquiv.apply_symm_apply, ← hγ, hy]
  let R' : Sylow 2 SL(2, GaloisField 2 f) := R.mapSurjective (f := e'.toMonoidHom) e'.surjective
  have hR' : (R' : Subgroup SL(2, GaloisField 2 f)) = (R : Subgroup X).map e'.toMonoidHom := rfl
  have hγR : ∀ r ∈ (R' : Subgroup SL(2, GaloisField 2 f)),
      γ r ∈ (R' : Subgroup SL(2, GaloisField 2 f)) := by
    intro r hr
    rw [hR', AschbacherToolkit.Bender.AutTransport.mem_map_iff'] at hr ⊢
    rw [hγapp, MulEquiv.symm_apply_apply]
    exact hαR _ hr
  have h1 := card_fix_sq_le_of_sq_inner_sl2 hf γ hγγ hγout R' hγR
  have hmem : ∀ r : (R : Subgroup X), e' r ∈ (R' : Subgroup SL(2, GaloisField 2 f)) := fun r =>
    (AschbacherToolkit.Bender.AutTransport.mem_map_iff e').mpr r.2
  let φ : {r : (R : Subgroup X) // α r = r} →
      {r : (R' : Subgroup SL(2, GaloisField 2 f)) // γ r = r} := fun r =>
    ⟨⟨e' r.1, hmem r.1⟩, by
      show γ (e' r.1) = e' r.1
      rw [hγapp, MulEquiv.symm_apply_apply, r.2]⟩
  have hφ : Function.Injective φ := by
    intro r r' h
    have h1 : e' (r.1 : X) = e' (r'.1 : X) :=
      congrArg (fun x : {r : (R' : Subgroup SL(2, GaloisField 2 f)) // γ r = r} =>
        (x.1 : SL(2, GaloisField 2 f))) h
    exact Subtype.ext (Subtype.ext (e'.injective h1))
  have hcard : Nat.card (R' : Subgroup SL(2, GaloisField 2 f)) = Nat.card (R : Subgroup X) := by
    rw [hR']
    exact Subgroup.card_map_of_injective e'.injective
  calc Nat.card {r : (R : Subgroup X) // α r = r} ^ 2
      ≤ Nat.card {r : (R' : Subgroup SL(2, GaloisField 2 f)) // γ r = r} ^ 2 :=
        Nat.pow_le_pow_left (Nat.card_le_card_of_injective φ hφ) 2
    _ ≤ Nat.card (R : Subgroup X) := hcard ▸ h1

theorem mul_inv_inner_of_sq_inner_psl2 {X : Type*} [Group X]
    [Finite X] (hf : 2 ≤ f) (e : X ≃* PSL(2, GaloisField 2 f)) {α β : MulAut X}
    (hαα : ∃ y, α * α = MulAut.conj y) (hββ : ∃ y, β * β = MulAut.conj y)
    (hα : ¬ ∃ y, α = MulAut.conj y) (hβ : ¬ ∃ y, β = MulAut.conj y) (R : Sylow 2 X)
    (hαR : ∀ r ∈ (R : Subgroup X), α r ∈ (R : Subgroup X))
    (hβR : ∀ r ∈ (R : Subgroup X), β r ∈ (R : Subgroup X)) :
    ∃ y, α * β⁻¹ = MulAut.conj y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e' : X ≃* SL(2, GaloisField 2 f) := e.trans CFSG.Walter.psl2MulEquivSL2OfCharTwo
  have happ : ∀ (δ : MulAut X) r, MulAut.congr e' δ r = e' (δ (e'.symm r)) := fun δ r => by
    have h := AschbacherToolkit.Bender.AutTransport.congr_apply' e' δ (e'.symm r)
    rwa [MulEquiv.apply_symm_apply] at h
  have hsq : ∀ δ : MulAut X, (∃ y, δ * δ = MulAut.conj y) →
      ∃ y, MulAut.congr e' δ * MulAut.congr e' δ = MulAut.conj y := by
    rintro δ ⟨y, hy⟩
    exact ⟨e' y, by rw [← map_mul, hy, AschbacherToolkit.Bender.AutTransport.congr_conj]⟩
  have hout : ∀ δ : MulAut X, (¬ ∃ y, δ = MulAut.conj y) →
      ¬ ∃ y, MulAut.congr e' δ = MulAut.conj y := by
    rintro δ hδ ⟨y, hy⟩
    apply hδ
    refine ⟨e'.symm y, (MulAut.congr e').injective ?_⟩
    rw [AschbacherToolkit.Bender.AutTransport.congr_conj, MulEquiv.apply_symm_apply, hy]
  let R' : Sylow 2 SL(2, GaloisField 2 f) := R.mapSurjective (f := e'.toMonoidHom) e'.surjective
  have hR' : (R' : Subgroup SL(2, GaloisField 2 f)) = (R : Subgroup X).map e'.toMonoidHom := rfl
  have hmaps : ∀ δ : MulAut X, (∀ r ∈ (R : Subgroup X), δ r ∈ (R : Subgroup X)) →
      ∀ r ∈ (R' : Subgroup SL(2, GaloisField 2 f)),
        MulAut.congr e' δ r ∈ (R' : Subgroup SL(2, GaloisField 2 f)) := by
    intro δ hδ r hr
    rw [hR', AschbacherToolkit.Bender.AutTransport.mem_map_iff'] at hr ⊢
    rw [happ, MulEquiv.symm_apply_apply]
    exact hδ _ hr
  obtain ⟨y, hy⟩ := mul_inv_inner_of_sq_inner_sl2 hf (hsq α hαα) (hsq β hββ) (hout α hα)
    (hout β hβ) R' (hmaps α hαR) (hmaps β hβR)
  refine ⟨e'.symm y, (MulAut.congr e').injective ?_⟩
  rw [AschbacherToolkit.Bender.AutTransport.congr_conj, MulEquiv.apply_symm_apply, map_mul,
    map_inv, hy]

theorem inner_of_sq_inner_of_odd_psl2 {X : Type*} [Group X]
    [Finite X] (hf : 2 ≤ f) (hodd : Odd f) (e : X ≃* PSL(2, GaloisField 2 f)) {α : MulAut X}
    (hαα : ∃ y, α * α = MulAut.conj y) (R : Sylow 2 X)
    (hαR : ∀ r ∈ (R : Subgroup X), α r ∈ (R : Subgroup X)) : ∃ y, α = MulAut.conj y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e' : X ≃* SL(2, GaloisField 2 f) := e.trans CFSG.Walter.psl2MulEquivSL2OfCharTwo
  have happ : ∀ r, MulAut.congr e' α r = e' (α (e'.symm r)) := fun r => by
    have h := AschbacherToolkit.Bender.AutTransport.congr_apply' e' α (e'.symm r)
    rwa [MulEquiv.apply_symm_apply] at h
  have hsq : ∃ y, MulAut.congr e' α * MulAut.congr e' α = MulAut.conj y := by
    obtain ⟨y, hy⟩ := hαα
    exact ⟨e' y, by rw [← map_mul, hy, AschbacherToolkit.Bender.AutTransport.congr_conj]⟩
  let R' : Sylow 2 SL(2, GaloisField 2 f) := R.mapSurjective (f := e'.toMonoidHom) e'.surjective
  have hR' : (R' : Subgroup SL(2, GaloisField 2 f)) = (R : Subgroup X).map e'.toMonoidHom := rfl
  have hmaps : ∀ r ∈ (R' : Subgroup SL(2, GaloisField 2 f)),
      MulAut.congr e' α r ∈ (R' : Subgroup SL(2, GaloisField 2 f)) := by
    intro r hr
    rw [hR', AschbacherToolkit.Bender.AutTransport.mem_map_iff'] at hr ⊢
    rw [happ, MulEquiv.symm_apply_apply]
    exact hαR _ hr
  obtain ⟨y, hy⟩ := inner_of_sq_inner_of_odd_sl2 hf hodd _ hsq R' hmaps
  refine ⟨e'.symm y, (MulAut.congr e').injective ?_⟩
  rw [AschbacherToolkit.Bender.AutTransport.congr_conj, MulEquiv.apply_symm_apply, hy]

end CFSG.ComponentClassification.GMS78
