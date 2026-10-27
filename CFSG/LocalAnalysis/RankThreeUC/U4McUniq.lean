module

public import CFSG.LocalAnalysis.RankThreeUC.U4McOff
import CFSG.ClassicalInvolution.Asc77.AscSCH19

public section

namespace CFSG.LocalAnalysis.RankThreeUC.U4Mc

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.Quasithin CFSG.Open
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)

variable {S : Type} [CommGroup S] {F : Type} [Field F]

theorem card_le_of_isPGroup_statedSU [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = (2 ^ n) ^ 2) {K : Subgroup ↥(StatedSU 4 (2 ^ n) F)} {k : ℕ}
    (hk : Nat.card K = 2 ^ k) : Nat.card K ≤ (2 ^ n) ^ 6 := by
  have hcard := CFSG.ClassicalInvolution.Asc77.SCH.card_statedSU_four (K := F) (ℓ := 2) (f := n)
    ⟨Nat.prime_two, hn, by rw [hF, ← pow_mul, mul_comm]⟩
  have hdvd : Nat.card K ∣ Nat.card ↥(StatedSU 4 (2 ^ n) F) := Subgroup.card_subgroup_dvd_card K
  have hev : Even (2 ^ n) := (Nat.even_pow' (by omega)).mpr even_two
  have hev2 : Even ((2 ^ n) ^ 2) := (Nat.even_pow' two_ne_zero).mpr hev
  have hev3 : Even ((2 ^ n) ^ 3) := (Nat.even_pow' (by norm_num)).mpr hev
  have hev4 : Even ((2 ^ n) ^ 4) := (Nat.even_pow' (by norm_num)).mpr hev
  have hodd : Odd (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) * ((2 ^ n) ^ 4 - 1)) := by
    have h1 : Odd ((2 ^ n) ^ 2 - 1) :=
      Nat.Even.sub_odd (Nat.one_le_pow _ _ (by positivity)) hev2 odd_one
    have h2 : Odd ((2 ^ n) ^ 3 + 1) := hev3.add_one
    have h3 : Odd ((2 ^ n) ^ 4 - 1) :=
      Nat.Even.sub_odd (Nat.one_le_pow _ _ (by positivity)) hev4 odd_one
    exact (h1.mul h2).mul h3
  have hcard' : Nat.card ↥(StatedSU 4 (2 ^ n) F) =
      (2 ^ n) ^ 6 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) * ((2 ^ n) ^ 4 - 1)) := by
    rw [hcard]
    ring
  rw [hcard', hk] at hdvd
  have hcop : Nat.Coprime (2 ^ k) (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) * ((2 ^ n) ^ 4 - 1)) :=
    (Nat.coprime_two_left.mpr hodd).pow_left k
  rw [hk]
  exact Nat.le_of_dvd (by positivity) (hcop.dvd_of_dvd_mul_right hdvd)

theorem eq_plane_of_offenders [Finite S] [Finite F] [CharP F 2] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = (2 ^ n) ^ 2) {L : Subgroup (MulAut S)} (N : NatSU4 n L F)
    {H A₁ A₂ : Subgroup (MulAut S)} (hH : IsPGroup 2 H) (hA₁H : A₁ ≤ H) (hA₂H : A₂ ≤ H)
    (hA₁L : A₁ ≤ L) (hA₂L : A₂ ≤ L) (hc₁ : Nat.card F ^ 2 ≤ Nat.card A₁)
    (hc₂ : Nat.card F ^ 2 ≤ Nat.card A₂) {W₁ W₂ : Submodule F (Fin 4 → F)}
    (hW₁2 : Module.finrank F W₁ = 2) (hW₂2 : Module.finrank F W₂ = 2)
    (hq₁ : ∀ a ∈ A₁, ∀ s : S, N.vec (a s) - N.vec s ∈ W₁)
    (hf₁ : ∀ s : S, s ∈ fixV A₁ ↔ N.vec s ∈ W₁) (hf₂ : ∀ s : S, s ∈ fixV A₂ ↔ N.vec s ∈ W₂) :
    W₁ = W₂ := by
  by_contra hne
  set σ := unitaryInvolution F 2 n with hσdef
  have hσ : IsUnitaryInvolution σ := isUnitaryInvolution_unitaryInvolution hF
  have hSU : SUid σ 4 = StatedSU 4 (2 ^ n) F := SUid_eq_statedSU hF 4
  set D := A₁ ⊓ A₂ with hD
  have hDL : D ≤ L := inf_le_left.trans hA₁L
  set Dm : Subgroup (GL (Fin 4) F) :=
    ((D.subgroupOf L).map N.ε.toMonoidHom).map (StatedSU 4 (2 ^ n) F).subtype with hDm
  have hDmcard : Nat.card Dm = Nat.card D := by
    rw [hDm, Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
      Subgroup.card_map_of_injective N.ε.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDL).toEquiv
  have hDmU : Dm ≤ SUid σ 4 := by
    rintro _ ⟨_, ⟨l, -, rfl⟩, rfl⟩
    rw [hSU]
    exact (N.ε l).2
  have hDact : ∀ g ∈ Dm, ∃ l : ↥L, (l : MulAut S) ∈ D ∧
      (g : Matrix (Fin 4) (Fin 4) F) = N.mat l := by
    rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    exact ⟨l, hl, rfl⟩
  have hfixW : ∀ {A : Subgroup (MulAut S)} {W : Submodule F (Fin 4 → F)},
      (∀ s : S, s ∈ fixV A ↔ N.vec s ∈ W) → ∀ l : ↥L, (l : MulAut S) ∈ A →
        ∀ w ∈ W, N.mat l *ᵥ w = w := by
    intro A W hf l hl w hw
    obtain ⟨s, rfl⟩ := N.exists_vec w
    rw [← N.vec_apply, ((hf s).mpr hw) _ hl]
  have hsq := card_sq_le_of_two_planes hσ Dm hDmU hW₁2 hW₂2 hne fun g hg => by
    obtain ⟨l, hl, hgl⟩ := hDact g hg
    rw [hgl]
    refine ⟨hfixW hf₁ l hl.1, hfixW hf₂ l hl.2, fun x => ?_⟩
    obtain ⟨s, rfl⟩ := N.exists_vec x
    rw [← N.vec_apply]
    exact hq₁ _ hl.1 s
  rw [hDmcard] at hsq
  set K := H ⊓ L with hK
  have : Finite (MulAut S) := Finite.of_injective _ DFunLike.coe_injective
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKcard : Nat.card K ≤ Nat.card F ^ 3 := by
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (hH.to_le (inf_le_left : K ≤ H))
    have hKL : Nat.card ↥((K.subgroupOf L).map N.ε.toMonoidHom) = Nat.card K := by
      rw [Subgroup.card_map_of_injective N.ε.injective]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : K ≤ L)).toEquiv
    have h := card_le_of_isPGroup_statedSU hn hF (hKL.trans hj)
    rw [hKL] at h
    rw [hF, ← pow_mul]
    exact h
  have hA₁K : A₁ ≤ K := le_inf hA₁H hA₁L
  have hA₂K : A₂ ≤ K := le_inf hA₂H hA₂L
  have e1 := Subgroup.relIndex_mul_card A₁ A₂
  have e2 := Subgroup.relIndex_mul_card A₁ K
  rw [inf_eq_left.mpr hA₁K] at e2
  have hK0 : Nat.card K ≠ 0 := Nat.card_pos.ne'
  have hidx : A₁.relIndex A₂ ≤ A₁.relIndex K :=
    Subgroup.relIndex_le_of_le_right hA₂K
      (left_ne_zero_of_mul (by rw [e2]; exact hK0 : A₁.relIndex K * Nat.card A₁ ≠ 0))
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  set f := Nat.card F
  set d := Nat.card ↥(A₁ ⊓ A₂)
  have h1 : f ^ 2 * f ^ 2 ≤ Nat.card A₁ * Nat.card A₂ := Nat.mul_le_mul hc₁ hc₂
  have h2 : Nat.card A₁ * Nat.card A₂ ≤ Nat.card K * d := by
    rw [← e1, ← e2]
    calc Nat.card A₁ * (A₁.relIndex A₂ * d) ≤ Nat.card A₁ * (A₁.relIndex K * d) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hidx)
      _ = A₁.relIndex K * Nat.card A₁ * d := by ring
  have h3 : f ^ 3 * f ≤ f ^ 3 * d := by
    calc f ^ 3 * f = f ^ 2 * f ^ 2 := by ring
      _ ≤ Nat.card K * d := h1.trans h2
      _ ≤ f ^ 3 * d := Nat.mul_le_mul_right _ hKcard
  have hfd : f ≤ d := Nat.le_of_mul_le_mul_left h3 (by positivity)
  have : f * f ≤ f := by
    calc f * f ≤ d * d := Nat.mul_le_mul hfd hfd
      _ = d ^ 2 := by ring
      _ ≤ f := hsq
  nlinarith

theorem exists_plane_of_offenders [Finite S] (hS : ∀ s : S, s ^ 2 = 1) [Finite F] [CharP F 2]
    {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = (2 ^ n) ^ 2) {L : Subgroup (MulAut S)}
    (N : NatSU4 n L F) {H : Subgroup (MulAut S)} (hH : IsPGroup 2 H)
    (hHN : H ≤ Subgroup.normalizer (L : Set (MulAut S))) {A₀ : Subgroup (MulAut S)}
    (hA₀H : A₀ ≤ H) (hA₀ : IsElemAbelian2 A₀) (hA₀1 : A₀ ≠ ⊥)
    (hA₀off : Nat.card S ≤ Nat.card A₀ * Nat.card (fixV A₀)) :
    ∃ W : Submodule F (Fin 4 → F), IsTI (unitaryInvolution F 2 n) W ∧ Module.finrank F W = 2 ∧
      (∀ A : Subgroup (MulAut S), A ≤ H → IsElemAbelian2 A →
        Nat.card S ≤ Nat.card A * Nat.card (fixV A) →
        A ≤ L ∧ (∀ a ∈ A, ∀ s : S, N.vec (a s) - N.vec s ∈ W) ∧
          ∀ a ∈ A, ∀ s : S, N.vec s ∈ W → a s = s) ∧
      ∀ h ∈ H, ∀ s : S, N.vec s ∈ W → N.vec (h s) ∈ W := by
  obtain ⟨hA₀L, hc₀, W, hWti, hW2, hq₀, hf₀⟩ :=
    exact_offender hS hn hF N hA₀ (hA₀H.trans hHN) hA₀1 hA₀off
  have hplane : ∀ A : Subgroup (MulAut S), A ≤ H → IsElemAbelian2 A → A ≠ ⊥ →
      Nat.card S ≤ Nat.card A * Nat.card (fixV A) →
      A ≤ L ∧ (∀ a ∈ A, ∀ s : S, N.vec (a s) - N.vec s ∈ W) ∧
        ∀ s : S, s ∈ fixV A ↔ N.vec s ∈ W := by
    intro A hAH hA hA1 hAoff
    obtain ⟨hAL, hcA, WA, -, hWA2, hqA, hfA⟩ :=
      exact_offender hS hn hF N hA (hAH.trans hHN) hA1 hAoff
    have hWA : W = WA :=
      eq_plane_of_offenders hn hF N hH hA₀H hAH hA₀L hAL hc₀ hcA hW2 hWA2 hq₀ hf₀ hfA
    rw [← hWA] at hqA hfA
    exact ⟨hAL, hqA, hfA⟩
  refine ⟨W, hWti, hW2, fun A hAH hA hAoff => ?_, fun h hh s hs => ?_⟩
  · by_cases hA1 : A = ⊥
    · subst hA1
      refine ⟨bot_le, fun a ha s => ?_, fun a ha s _ => ?_⟩
      · rw [Subgroup.mem_bot.mp ha, MulAut.one_apply, sub_self]
        exact W.zero_mem
      · rw [Subgroup.mem_bot.mp ha, MulAut.one_apply]
    · obtain ⟨hAL, hqA, hfA⟩ := hplane A hAH hA hA1 hAoff
      exact ⟨hAL, hqA, fun a ha s hs => (hfA s).mpr hs a ha⟩
  ·
    set A₁ := A₀.map (MulAut.conj h).toMonoidHom with hA₁def
    have hA₁H : A₁ ≤ H := by
      rintro _ ⟨a, ha, rfl⟩
      exact H.mul_mem (H.mul_mem hh (hA₀H ha)) (H.inv_mem hh)
    have hA₁ : IsElemAbelian2 A₁ := by
      refine ⟨?_, ?_⟩
      · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        rw [← map_mul, ← map_mul, hA₀.1 a ha b hb]
      · rintro _ ⟨a, ha, rfl⟩
        rw [← map_pow, hA₀.2 a ha, map_one]
    have hA₁1 : A₁ ≠ ⊥ := by
      rw [hA₁def, Ne, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj h).injective]
      exact hA₀1
    have hfix₁ : ∀ t : S, t ∈ fixV A₀ ↔ h t ∈ fixV A₁ := by
      intro t
      constructor
      · rintro ht _ ⟨a, ha, rfl⟩
        show (h * a * h⁻¹) (h t) = h t
        rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, ht a ha]
      · intro ht a ha
        have h1 := ht _ ⟨a, ha, rfl⟩
        change (h * a * h⁻¹) (h t) = h t at h1
        rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self] at h1
        exact h.injective h1
    have hcardfix : Nat.card (fixV A₁) = Nat.card (fixV A₀) :=
      (Nat.card_congr (Equiv.subtypeEquiv h.toEquiv hfix₁)).symm
    have hcard₁ : Nat.card A₁ = Nat.card A₀ :=
      Subgroup.card_map_of_injective (MulAut.conj h).injective
    obtain ⟨-, -, hf₁⟩ := hplane A₁ hA₁H hA₁ hA₁1 (by rw [hcard₁, hcardfix]; exact hA₀off)
    exact (hf₁ (h s)).mp ((hfix₁ s).mp ((hf₀ s).mpr hs))

theorem sub_mem_of_fix_plane [Finite F] [CharP F 2] {n : ℕ} (hF : Nat.card F = (2 ^ n) ^ 2)
    {L : Subgroup (MulAut S)} (N : NatSU4 n L F) {W : Submodule F (Fin 4 → F)}
    (hW : IsTI (unitaryInvolution F 2 n) W) (hW2 : Module.finrank F W = 2) {l : ↥L}
    (hl : ∀ s : S, N.vec s ∈ W → (l : MulAut S) s = s) (s : S) :
    N.vec ((l : MulAut S) s) - N.vec s ∈ W := by
  refine hW.mem_of_herm_eq_zero hW2 fun w hw => ?_
  obtain ⟨t, rfl⟩ := N.exists_vec w
  have hlt : N.mat l *ᵥ N.vec t = N.vec t := by rw [← N.vec_apply, hl t hw]
  rw [herm_sub_right, N.vec_apply]
  conv_lhs => rw [← hlt]
  rw [N.herm_mat hF l, hlt, sub_self]

theorem exists_conj_stab_plane [Finite S] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = (2 ^ n) ^ 2) (hn : Even n) {L : Subgroup (MulAut S)} (N : NatSU4 n L F)
    {W : Submodule F (Fin 4 → F)} (hW : IsTI (unitaryInvolution F 2 n) W)
    (hW2 : Module.finrank F W = 2) (b : ↥L) (hb3 : b ^ 3 = 1)
    (hbfix : ∀ s : S, (b : MulAut S) s = s → s = 1) :
    ∃ g : ↥L, ∀ l : ↥L, l * (g * b * g⁻¹) = g * b * g⁻¹ * l →
      ∀ s : S, N.vec s ∈ W → N.vec ((l : MulAut S) s) ∈ W := by
  set σ := unitaryInvolution F 2 n with hσdef
  have hσ : IsUnitaryInvolution σ := isUnitaryInvolution_unitaryInvolution hF
  have hSU : SUid σ 4 = StatedSU 4 (2 ^ n) F := SUid_eq_statedSU hF 4
  have h2F : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hMiso : ∀ x y, herm σ (N.mat b *ᵥ x) (N.mat b *ᵥ y) = herm σ x y := N.herm_mat hF b
  have hM3 : ∀ v, N.mat b *ᵥ (N.mat b *ᵥ (N.mat b *ᵥ v)) = v := by
    intro v
    obtain ⟨s, rfl⟩ := N.exists_vec v
    rw [← N.vec_apply, ← N.vec_apply, ← N.vec_apply]
    congr 1
    have h3 : ((b ^ 3 : ↥L) : MulAut S) s = s := by rw [hb3]; rfl
    rw [pow_succ, pow_succ, pow_one, Subgroup.coe_mul, Subgroup.coe_mul, MulAut.mul_apply,
      MulAut.mul_apply] at h3
    exact h3
  have hMfix : ∀ v, N.mat b *ᵥ v = v → v = 0 := by
    intro v hv
    obtain ⟨s, rfl⟩ := N.exists_vec v
    rw [← N.vec_apply] at hv
    rw [hbfix s (N.vec_injective hv), N.vec_one]
  obtain ⟨ω, hω, hωq⟩ := exists_cubeRoot hF hn
  have hσω : σ ω = ω := by rw [hσdef, unitaryInvolution_apply, hωq]
  have hω1 : σ ω * ω ≠ 1 := by
    rw [hσω]
    intro h
    have hω0 : ω = 0 := by linear_combination hω - h - h2F
    rw [hω0, mul_zero] at h
    exact zero_ne_one h
  have hX2 := finrank_eigenSub h2F hMiso hM3 hMfix hω hσω
  have hXti := isTI_eigenSub hMiso hω1
  obtain ⟨γ, hγ⟩ := exists_smul_mem_of_isTI hσ hW hW2 hXti hX2
  let γ' : ↥(StatedSU 4 (2 ^ n) F) := ⟨γ, hSU ▸ γ.2⟩
  refine ⟨N.ε.symm (γ'⁻¹), fun l hl s hs => ?_⟩
  set b' := N.ε.symm (γ'⁻¹) * b * (N.ε.symm (γ'⁻¹))⁻¹ with hb'
  have hb'mat : ∀ x, N.mat b' *ᵥ x = (γ⁻¹ : SUid σ 4) • (N.mat b *ᵥ (γ • x)) := by
    intro x
    have hε : N.ε b' = γ'⁻¹ * N.ε b * γ' := by
      rw [hb']
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, inv_inv]
    rw [NatSU4.mat, hε, smul_def, smul_def, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul,
      Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rfl
  have hWe : ∀ w ∈ W, N.mat b' *ᵥ w = ω • w := by
    intro w hw
    rw [hb'mat, mem_eigenSub.mp (hγ w hw), smul_comm, inv_smul_smul]
  have hEti : IsTI σ (eigenSub (N.mat b') ω) := isTI_eigenSub (N.herm_mat hF b') hω1
  have hWeq : W = eigenSub (N.mat b') ω :=
    Submodule.eq_of_le_of_finrank_le (fun w hw => mem_eigenSub.mpr (hWe w hw))
      (by rw [hW2]; exact hEti.finrank_le)
  have hcomm : ∀ x, N.mat l *ᵥ (N.mat b' *ᵥ x) = N.mat b' *ᵥ (N.mat l *ᵥ x) := by
    intro x
    obtain ⟨t, rfl⟩ := N.exists_vec x
    rw [← N.vec_apply, ← N.vec_apply, ← N.vec_apply, ← N.vec_apply]
    congr 1
    have h1 := congrArg (fun z : ↥L => (z : MulAut S) t) hl
    simp only [Subgroup.coe_mul, MulAut.mul_apply] at h1
    exact h1
  rw [N.vec_apply, hWeq, mem_eigenSub, ← hcomm, hWe _ hs, Matrix.mulVec_smul]

end CFSG.LocalAnalysis.RankThreeUC.U4Mc
