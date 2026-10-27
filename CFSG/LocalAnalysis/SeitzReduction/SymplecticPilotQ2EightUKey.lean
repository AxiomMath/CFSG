module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightUModel
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightUCube
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2UnitaryCTAlign

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.Fischer.Classification (CubeRel)
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Bar

variable {F : Type} [Field F] {σ : F ≃+* F}

@[expose] noncomputable def barPow (hσ : ∀ c, σ (σ c) = c) (b : Bool) :
    MulAut (SU σ (2 * 4 + 0)) :=
  bif b then ctuaBarAut σ hσ (2 * 4 + 0) else 1

theorem coe_barPow (hσ : ∀ c, σ (σ c) = c) (b : Bool) (x : SU σ (2 * 4 + 0)) :
    (((barPow hσ b x : SU σ (2 * 4 + 0)) : GL (Fin (2 * 4 + 0)) F) :
      Matrix (Fin (2 * 4 + 0)) (Fin (2 * 4 + 0)) F) =
        bif b then
          ((x : GL (Fin (2 * 4 + 0)) F) : Matrix (Fin (2 * 4 + 0)) (Fin (2 * 4 + 0)) F).map σ
          else ((x : GL (Fin (2 * 4 + 0)) F) : Matrix (Fin (2 * 4 + 0)) (Fin (2 * 4 + 0)) F) := by
  cases b
  · rfl
  · rfl

theorem barPow_mem_ctuBlock_iff (hσ : ∀ c, σ (σ c) = c) (b : Bool) (R : Finset (Fin 4))
    (x : SU σ (2 * 4 + 0)) : barPow hσ b x ∈ ctuBlock σ 0 R ↔ x ∈ ctuBlock σ 0 R := by
  have h1 : ∀ a b' : Fin (2 * 4 + 0),
      σ ((1 : Matrix (Fin (2 * 4 + 0)) (Fin (2 * 4 + 0)) F) a b') =
        (1 : Matrix (Fin (2 * 4 + 0)) (Fin (2 * 4 + 0)) F) a b' := fun a b' => by
    rw [Matrix.one_apply]
    split_ifs <;> simp
  rw [mem_ctuBlock, mem_ctuBlock]
  refine forall_congr' fun a => forall_congr' fun b' => imp_congr_right fun _ => ?_
  rw [coe_barPow]
  cases b
  · rfl
  · change σ _ = _ ↔ _
    constructor
    · intro h
      apply σ.injective
      rw [h, h1]
    · intro h
      rw [h, h1]

theorem ctuaTwist_zero_eq_barPow (hσ : ∀ c, σ (σ c) = c) {ν : Fˣ} (hν : σ ν * ν = 1) (b : Bool)
    (x : SU σ (2 * 4 + 0)) :
    ctuaTwist (N := 4) (Nat.zero_le 1) σ hσ ν hν b x = barPow hσ b x := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [ctuaTwist_apply_apply, coe_barPow]
  obtain ⟨w, rfl⟩ := (ctuCoord 4 0).surjective i
  obtain ⟨w', rfl⟩ := (ctuCoord 4 0).surjective j
  rcases w with u | k
  · rcases w' with v | l
    · rw [ctuaTorEntry_inl, ctuaTorEntry_inl, one_mul, mul_one]
      cases b <;> rfl
    · exact l.elim0
  · exact k.elim0

end Bar

section Conj

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {F : Type} [Field F] [Finite F] [CharP F 2] {ι : K →+* F}
  {hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c} {e : L ≃* StatedSp 4 K}

theorem NsUniParam.overlap_eq (hF : Nat.card F = (2 ^ 1) ^ 2) {k l : Fin 4} (hkl : k ≠ l)
    (P : NsUniParam 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι e k) :
    ((ctuBlock (unitaryInvolution F 2 1) 0 ({k, l} : Finset (Fin 4))).subgroupOf
      (ctuBlock (unitaryInvolution F 2 1) 0 ({k} : Finset (Fin 4)))).map P.Φ =
        centralizerPerfectCore (modelToG e (nsTorusSp K k ⊔ nsTorusSp K l)) := by
  rw [P.map_overlap_eq hF le_rfl hkl, UnitaryPilot.modelToG_sup]

theorem NsUniParam.exists_barPow_of_conj (hK : Nat.card K = 2) (hF : Nat.card F = (2 ^ 1) ^ 2)
    {k l : Fin 4} (hkl : k ≠ l)
    (P : NsUniParam 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι e k) {h : G}
    (hN : h ∈ normalizer (centralizerPerfectCore (modelToG e (nsTorusSp K k ⊔ nsTorusSp K l)) :
      Set G))
    (hfix : ∀ y ∈ spBlock K ({k, l} : Finset (Fin 4))ᶜ,
      h * ((e.symm y : L) : G) = ((e.symm y : L) : G) * h) :
    ∃ b : Bool, ∀ (x : SU (unitaryInvolution F 2 1) (2 * 4 + 0))
      (hx : x ∈ ctuBlock (unitaryInvolution F 2 1) 0 ({k, l} : Finset (Fin 4))),
      h * P.Φ ⟨x, ctuBlock_pair_le_left _ k l hx⟩ * h⁻¹ =
        P.Φ ⟨barPow (unitaryInvolution_involutive hF) b x, ctuBlock_pair_le_left _ k l
          ((barPow_mem_ctuBlock_iff _ b _ x).2 hx)⟩ := by
  classical
  set σ := unitaryInvolution F 2 1 with hσdef
  set B := ctuBlock σ 0 ({k, l} : Finset (Fin 4)) with hB
  set φ : B →* G := P.Φ.comp (Subgroup.inclusion (ctuBlock_pair_le_left σ k l)) with hφ
  have hφapp : ∀ z : B, φ z = P.Φ ⟨z, ctuBlock_pair_le_left σ k l z.2⟩ := fun z => rfl
  have hφinj : Function.Injective φ := fun x y hxy => by
    have h' := P.injOn_ctuBlock hF (by norm_num) hkl (x := ⟨x, ctuBlock_pair_le_left σ k l x.2⟩)
      (y := ⟨y, ctuBlock_pair_le_left σ k l y.2⟩) (ctuBlock_pair_le_right σ k l x.2)
      (ctuBlock_pair_le_right σ k l y.2) hxy
    exact Subtype.ext (congrArg (fun w : ctuBlock σ 0 ({k} : Finset (Fin 4)) =>
      (w : SU σ (2 * 4 + 0))) h')
  have hover := P.overlap_eq hF hkl
  have hex : ∀ z : B, ∃ z' : B, h * φ z * h⁻¹ = φ z' := by
    intro z
    have hz : φ z ∈ centralizerPerfectCore (modelToG e (nsTorusSp K k ⊔ nsTorusSp K l)) := by
      rw [← hover]
      exact ⟨⟨z, ctuBlock_pair_le_left σ k l z.2⟩, mem_subgroupOf.2 z.2, rfl⟩
    have hz' := (mem_normalizer_iff.1 hN (φ z)).1 hz
    rw [← hover] at hz'
    obtain ⟨w, hw, hw'⟩ := hz'
    exact ⟨⟨w, mem_subgroupOf.1 hw⟩, hw'.symm⟩
  choose f hf using hex
  have hfmul : ∀ z w : B, f (z * w) = f z * f w := fun z w => hφinj (by
    rw [← hf, map_mul, map_mul, ← hf, ← hf]
    group)
  have hfinj : Function.Injective f := fun z w hzw => hφinj (by
    have h1 := hf z
    have h2 := hf w
    rw [hzw, ← h2] at h1
    have h3 := congrArg (fun g => h⁻¹ * g * h) h1
    simpa [mul_assoc] using h3)
  have : Finite (GL (Fin (2 * 4 + 0)) F) :=
    Finite.of_injective (fun u : GL (Fin (2 * 4 + 0)) F =>
      (u : Matrix (Fin (2 * 4 + 0)) (Fin (2 * 4 + 0)) F)) fun _ _ h => Units.ext h
  set α : MulAut B := MulEquiv.ofBijective (MonoidHom.mk' f hfmul)
    ⟨hfinj, Finite.surjective_of_injective hfinj⟩ with hα
  have hαapp : ∀ z : B, φ (α z) = h * φ z * h⁻¹ := fun z => (hf z).symm
  have hRc : 2 ≤ ({k, l} : Finset (Fin 4))ᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hkl]
  have hfixα : ∀ (y : StatedSp 4 K) (hy : y ∈ spBlock K ({k, l} : Finset (Fin 4))ᶜ),
      α ⟨ctuEmbed 0 (Nat.zero_le 1) σ ι hι y, ctuEmbed_mem_ctuBlock_iff.2 hy⟩ =
        ⟨ctuEmbed 0 (Nat.zero_le 1) σ ι hι y, ctuEmbed_mem_ctuBlock_iff.2 hy⟩ := by
    intro y hy
    apply hφinj
    have hyk : y ∈ spBlock K ({k} : Finset (Fin 4))ᶜ :=
      spBlock_mono (Finset.compl_subset_compl.2 (by simp)) hy
    have hφy : φ ⟨ctuEmbed 0 (Nat.zero_le 1) σ ι hι y, ctuEmbed_mem_ctuBlock_iff.2 hy⟩ =
        ((e.symm y : L) : G) := P.N1 y hyk
    rw [hαapp, hφy, hfix y hy, mul_inv_cancel_right]
  obtain ⟨ν, hν, b, hb⟩ := exists_ctuaTwist_of_mulAut_fix (by rw [hK, pow_one]) hF le_rfl
    (Nat.zero_le 1) hι hRc α hfixα
  refine ⟨b, fun x hx => ?_⟩
  have h1 := hαapp ⟨x, hx⟩
  rw [hφapp, hφapp] at h1
  rw [← h1]
  congr 1
  apply Subtype.ext
  change ((α ⟨x, hx⟩ : B) : SU σ (2 * 4 + 0)) = _
  rw [hb, ctuaTwist_zero_eq_barPow]

omit [Finite G] in
theorem NsUniParam.false_of_overlap_conj_le (hK : Nat.card K = 2)
    (hF : Nat.card F = (2 ^ 1) ^ 2) {k l : Fin 4} (hkl : k ≠ l)
    (P : NsUniParam 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι e k) {m : Fin 4}
    (hm : nsElt (K := K) m ∈ spBlock K ({k, l} : Finset (Fin 4))ᶜ)
    {g : SU (unitaryInvolution F 2 1) (2 * 4 + 0)}
    (hg : g ∈ ctuBlock (unitaryInvolution F 2 1) 0 ({k, l} : Finset (Fin 4)))
    (hR : CubeRel (ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι (nsElt (K := K) m))
      (g * ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι (nsElt (K := K) m) * g⁻¹))
    (hne : ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι (nsElt (K := K) m) *
        (g * ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι (nsElt (K := K) m) * g⁻¹) ≠
      (g * ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι (nsElt (K := K) m) * g⁻¹) *
        ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι (nsElt (K := K) m))
    {q : G} (hq : q * ((e.symm (nsElt m) : L) : G) = ((e.symm (nsElt m) : L) : G) * q)
    (hL : ∀ (x : SU (unitaryInvolution F 2 1) (2 * 4 + 0))
      (hx : x ∈ ctuBlock (unitaryInvolution F 2 1) 0 ({k, l} : Finset (Fin 4))),
      q * P.Φ ⟨x, ctuBlock_pair_le_left _ k l hx⟩ * q⁻¹ ∈ L) : False := by
  classical
  let φ : ctuBlock (unitaryInvolution F 2 1) 0 ({k, l} : Finset (Fin 4)) →* G :=
    P.Φ.comp (Subgroup.inclusion (ctuBlock_pair_le_left (unitaryInvolution F 2 1) k l))
  have hφinj : Function.Injective φ := fun x y hxy => by
    have h' := P.injOn_ctuBlock hF (by norm_num) hkl
      (x := ⟨x, ctuBlock_pair_le_left (unitaryInvolution F 2 1) k l x.2⟩)
      (y := ⟨y, ctuBlock_pair_le_left (unitaryInvolution F 2 1) k l y.2⟩)
      (ctuBlock_pair_le_right (unitaryInvolution F 2 1) k l x.2)
      (ctuBlock_pair_le_right (unitaryInvolution F 2 1) k l y.2) hxy
    exact Subtype.ext (congrArg (fun w : ctuBlock (unitaryInvolution F 2 1) 0
      ({k} : Finset (Fin 4)) => (w : SU (unitaryInvolution F 2 1) (2 * 4 + 0))) h')
  let ψ₀ : ctuBlock (unitaryInvolution F 2 1) 0 ({k, l} : Finset (Fin 4)) →* L :=
    ((MulAut.conj q).toMonoidHom.comp φ).codRestrict L fun z => hL z z.2
  have hψ₀ : ∀ z, ((ψ₀ z : L) : G) = q * φ z * q⁻¹ := fun z => rfl
  let ψ : ctuBlock (unitaryInvolution F 2 1) 0 ({k, l} : Finset (Fin 4)) →* StatedSp 4 K :=
    e.toMonoidHom.comp ψ₀
  have hψ : ∀ z, ψ z = e (ψ₀ z) := fun z => rfl
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    apply hφinj
    have h1 := congrArg Subtype.val (e.injective ((hψ x).symm.trans (hxy.trans (hψ y))))
    rw [hψ₀, hψ₀] at h1
    simpa using h1
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : ctuBlock (unitaryInvolution F 2 1) 0 ({k, l} : Finset (Fin 4)),
      (x₁ : SU (unitaryInvolution F 2 1) (2 * 4 + 0)) =
        ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι (nsElt (K := K) m) :=
    ⟨⟨_, ctuEmbed_mem_ctuBlock_iff.2 hm⟩, rfl⟩
  obtain ⟨gB, hgB⟩ : ∃ gB : ctuBlock (unitaryInvolution F 2 1) 0 ({k, l} : Finset (Fin 4)),
      (gB : SU (unitaryInvolution F 2 1) (2 * 4 + 0)) = g := ⟨⟨g, hg⟩, rfl⟩
  have hR' : CubeRel x₁ (gB * x₁ * gB⁻¹) := by
    refine ⟨Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_⟩ <;>
      simp only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one, hx₁, hgB]
    · exact hR.cube_left
    · exact hR.cube_right
    · exact hR.cube_mul
    · exact hR.cube_mul_inv
  have hmk : nsElt (K := K) m ∈ spBlock K ({k} : Finset (Fin 4))ᶜ :=
    spBlock_mono (Finset.compl_subset_compl.2 (by simp)) hm
  have hψ1 : ψ x₁ = nsElt m := by
    have h1 : φ x₁ = ((e.symm (nsElt m) : L) : G) :=
      P.N1' hmk ⟨x₁, ctuBlock_pair_le_left (unitaryInvolution F 2 1) k l x₁.2⟩ hx₁
    have h2 : ψ₀ x₁ = e.symm (nsElt m) := by
      apply Subtype.ext
      rw [hψ₀, h1, hq, mul_inv_cancel_right]
    rw [hψ, h2, MulEquiv.apply_symm_apply]
  have hRψ : CubeRel (ψ x₁) (ψ (gB * x₁ * gB⁻¹)) :=
    ⟨by rw [← map_pow, hR'.cube_left, map_one], by rw [← map_pow, hR'.cube_right, map_one],
      by rw [← map_mul, ← map_pow, hR'.cube_mul, map_one],
      by rw [← map_inv, ← map_mul, ← map_pow, hR'.cube_mul_inv, map_one]⟩
  have hc := commute_of_cubeRel_of_conj_nsElt hK ⟨1, m, by rw [hψ1]; group⟩
    ⟨ψ gB, m, by rw [map_mul, map_mul, map_inv, hψ1]⟩ hRψ
  rw [← map_mul, ← map_mul] at hc
  have h3 := congrArg Subtype.val (hψinj hc)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hx₁, hgB] at h3
  exact hne h3

theorem mem_normalizer_of_map_conj_eq {P : Type*} [Group P] {H : Subgroup P} {x : P}
    (h : H.map (MulAut.conj x).toMonoidHom = H) : x ∈ normalizer (H : Set P) := by
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have h1 : x * y * x⁻¹ ∈ H.map (MulAut.conj x).toMonoidHom := ⟨y, hy, rfl⟩
    rwa [h] at h1
  · intro hy
    rw [← h] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hzy
    have : z = y := by
      have h2 := congrArg (fun w => x⁻¹ * w * x) hzy
      simpa [mul_assoc] using h2
    rwa [← this]

theorem NsUniParam.exists_eq_of_mem_overlap (hF : Nat.card F = (2 ^ 1) ^ 2) {k l : Fin 4}
    (hkl : k ≠ l) (P : NsUniParam 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι e k) {z : G}
    (hz : z ∈ centralizerPerfectCore (modelToG e (nsTorusSp K k ⊔ nsTorusSp K l))) :
    ∃ (x : SU (unitaryInvolution F 2 1) (2 * 4 + 0))
      (hx : x ∈ ctuBlock (unitaryInvolution F 2 1) 0 ({k, l} : Finset (Fin 4))),
      P.Φ ⟨x, ctuBlock_pair_le_left _ k l hx⟩ = z := by
  rw [← P.overlap_eq hF hkl] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  exact ⟨w, mem_subgroupOf.1 hw, rfl⟩

theorem NsUniParam.mem_overlap (hF : Nat.card F = (2 ^ 1) ^ 2) {k l : Fin 4} (hkl : k ≠ l)
    (P : NsUniParam 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι e k)
    {x : SU (unitaryInvolution F 2 1) (2 * 4 + 0)}
    (hx : x ∈ ctuBlock (unitaryInvolution F 2 1) 0 ({k, l} : Finset (Fin 4))) :
    P.Φ ⟨x, ctuBlock_pair_le_left _ k l hx⟩ ∈
      centralizerPerfectCore (modelToG e (nsTorusSp K k ⊔ nsTorusSp K l)) := by
  rw [← P.overlap_eq hF hkl]
  exact ⟨⟨x, ctuBlock_pair_le_left _ k l hx⟩, mem_subgroupOf.2 hx, rfl⟩

theorem NsUniParam.conj_t_eq_bar (hset : SeitzSetting G L) (hK : Nat.card K = 2)
    (hF : Nat.card F = (2 ^ 1) ^ 2) {k l : Fin 4} (hkl : k ≠ l)
    (P : NsUniParam 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι e k) {m : Fin 4}
    (hm : nsElt (K := K) m ∈ spBlock K ({k, l} : Finset (Fin 4))ᶜ)
    {g : SU (unitaryInvolution F 2 1) (2 * 4 + 0)}
    (hg : g ∈ ctuBlock (unitaryInvolution F 2 1) 0 ({k, l} : Finset (Fin 4)))
    (hR : CubeRel (ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι (nsElt (K := K) m))
      (g * ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι (nsElt (K := K) m) * g⁻¹))
    (hne : ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι (nsElt (K := K) m) *
        (g * ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι (nsElt (K := K) m) * g⁻¹) ≠
      (g * ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι (nsElt (K := K) m) * g⁻¹) *
        ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι (nsElt (K := K) m))
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    ∀ (x : SU (unitaryInvolution F 2 1) (2 * 4 + 0))
      (hx : x ∈ ctuBlock (unitaryInvolution F 2 1) 0 ({k, l} : Finset (Fin 4))),
      t * P.Φ ⟨x, ctuBlock_pair_le_left _ k l hx⟩ * t⁻¹ =
        P.Φ ⟨barPow (unitaryInvolution_involutive hF) true x, ctuBlock_pair_le_left _ k l
          ((barPow_mem_ctuBlock_iff _ true _ x).2 hx)⟩ := by
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hN := UnitaryPilot.mem_normalizer_centralizerPerfectCore_modelToG_of_mem_centralizer e htC
    (nsTorusSp K k ⊔ nsTorusSp K l)
  have hfix : ∀ y ∈ spBlock K ({k, l} : Finset (Fin 4))ᶜ,
      t * ((e.symm y : L) : G) = ((e.symm y : L) : G) * t := fun y _ =>
    (mem_centralizer_iff.1 htC _ (e.symm y).2).symm
  obtain ⟨b, hb⟩ := P.exists_barPow_of_conj hK hF hkl hN hfix
  cases b
  · exfalso
    have hOut : Group.IsSolvable (Outer L) :=
      isSolvable_outer_of_isCyclic (isCyclic_outer_of_mulEquiv_statedSp (by norm_num) e)
    have hperf := F4Pilot.commutator_centralizerPerfectCore
      (modelToG e (nsTorusSp K k ⊔ nsTorusSp K l))
    have hle : centralizerPerfectCore (modelToG e (nsTorusSp K k ⊔ nsTorusSp K l)) ≤
        centralizer ({t} : Set G) := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := P.exists_eq_of_mem_overlap hF hkl hz
      rw [mem_centralizer_singleton_iff]
      have h1 := hb x hx
      exact (mul_inv_eq_iff_eq_mul.1 h1).symm
    have hAL := std_perfect_le hset.standardSetting hOut htC ht hperf hle
    exact P.false_of_overlap_conj_le hK hF hkl hm hg hR hne (q := 1) (by group)
      fun x hx => by simpa using hAL (P.mem_overlap hF hkl hx)
  · exact hb

end Conj

section Key

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {F : Type} [Field F] [Finite F] [CharP F 2] {ι : K →+* F}
  {hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c} {e : L ≃* StatedSp 4 K}

omit [Finite F] [CharP F 2] in
theorem barPow_true_barPow_true {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) (x : SU σ (2 * 4 + 0)) :
    barPow hσ true (barPow hσ true x) = x :=
  Subtype.ext (Units.ext (by
    rw [coe_barPow, coe_barPow]
    ext i j
    simp only [Bool.cond_true, map_apply, hσ]))

omit [Finite K] [CharP K 2] in
theorem nsElt_mem_spBlock_compl_of_not_mem {k : Fin 4} {R : Finset (Fin 4)} (hk : k ∉ R) :
    nsElt (K := K) k ∈ spBlock K Rᶜ := by
  have h1 : nsElt (K := K) k ∈ spBlock K ({k} : Finset (Fin 4)) := by
    rw [spBlock_singleton]
    exact nsTorusSp_le_longRootSp2 k (nsElt_mem_nsTorusSp k)
  exact spBlock_mono (by simpa using hk) h1

theorem commute_permSp_swap_zero_one (hset : SeitzSetting G L) (hK : Nat.card K = 2)
    (hF : Nat.card F = (2 ^ 1) ^ 2)
    (P₀ : NsUniParam 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι e 0)
    (P₂ : NsUniParam 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι e 2) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (x : SU (unitaryInvolution F 2 1) (2 * 4 + 0))
    (hx : x ∈ ctuBlock (unitaryInvolution F 2 1) 0 ({0, 1} : Finset (Fin 4))) :
    ((e.symm (permSp K (Equiv.swap (0 : Fin 4) 1)) : L) : G) *
        P₀.Φ ⟨x, ctuBlock_pair_le_left _ 0 1 hx⟩ =
      P₀.Φ ⟨x, ctuBlock_pair_le_left _ 0 1 hx⟩ *
        ((e.symm (permSp K (Equiv.swap (0 : Fin 4) 1)) : L) : G) := by
  classical
  have hσ : ∀ c, unitaryInvolution F 2 1 (unitaryInvolution F 2 1 c) = c :=
    unitaryInvolution_involutive hF
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card CFSG.Fischer.F4 = Fintype.card F := by
    rw [CFSG.Fischer.F4.card, ← Nat.card_eq_fintype_card, hF]
    norm_num
  obtain ⟨φ4⟩ : Nonempty (CFSG.Fischer.F4 →+* F) :=
    ⟨(FiniteField.ringEquivOfCardEq (K := CFSG.Fischer.F4) (K' := F) hcard).toRingHom⟩
  have hτ := EightU.tauElt_mem_ctuBlock (F := F) φ4
  have hτb : barPow hσ true (EightU.tauElt φ4) ∈
      ctuBlock (unitaryInvolution F 2 1) 0 ({2, 3} : Finset (Fin 4)) :=
    (barPow_mem_ctuBlock_iff hσ true _ _).2 hτ
  have hτw := EightU.tauElt_inv_mul_bar φ4 (K := K) (ι := ι) hι hσ
  have hw23 : permSp K (Equiv.swap (0 : Fin 4) 1) ∈ spBlock K ({2, 3} : Finset (Fin 4))ᶜ := by
    rw [← ctuEmbed_mem_ctuBlock_iff (ε := 0) (hε := Nat.zero_le 1)
      (σ := unitaryInvolution F 2 1) (ι := ι) (hι := hι), ← hτw]
    exact mul_mem (inv_mem hτ) hτb
  have hcompl : ({2, 3} : Finset (Fin 4))ᶜ = {0, 1} := by decide
  have hw01 : permSp K (Equiv.swap (0 : Fin 4) 1) ∈ spBlock K ({0, 1} : Finset (Fin 4)) :=
    hcompl ▸ hw23
  have hw2 : permSp K (Equiv.swap (0 : Fin 4) 1) ∈ spBlock K ({2} : Finset (Fin 4))ᶜ :=
    spBlock_mono (Finset.compl_subset_compl.2 (by simp)) hw23
  have hmap : (nsTorusSp K (0 : Fin 4) ⊔ nsTorusSp K 1).map
      (MulAut.conj (permSp K (Equiv.swap (0 : Fin 4) 1))).toMonoidHom =
        nsTorusSp K 0 ⊔ nsTorusSp K 1 := by
    rw [Subgroup.map_sup, map_conj_permSp_nsTorusSp, map_conj_permSp_nsTorusSp,
      Equiv.swap_apply_left, Equiv.swap_apply_right, sup_comm]
  have hN := UnitaryPilot.symm_mem_normalizer_centralizerPerfectCore_modelToG e
    (mem_normalizer_of_map_conj_eq hmap)
  have hfix : ∀ y ∈ spBlock K ({0, 1} : Finset (Fin 4))ᶜ,
      ((e.symm (permSp K (Equiv.swap (0 : Fin 4) 1)) : L) : G) * ((e.symm y : L) : G) =
        ((e.symm y : L) : G) * ((e.symm (permSp K (Equiv.swap (0 : Fin 4) 1)) : L) : G) := by
    intro y hy
    have h1 := (commute_of_mem_spBlock_of_disjoint disjoint_compl_right hw01 hy).eq
    rw [← L.coe_mul, ← L.coe_mul, ← map_mul, ← map_mul, h1]
  obtain ⟨b, hb⟩ := P₀.exists_barPow_of_conj hK hF (by decide) hN hfix
  cases b
  · exact mul_inv_eq_iff_eq_mul.1 (hb x hx)
  exfalso
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hOut : Group.IsSolvable (Outer L) :=
    isSolvable_outer_of_isCyclic (isCyclic_outer_of_mulEquiv_statedSp (by norm_num) e)
  have hpair01 := EightU.cubeRel_ctuEmbed_nsElt_two φ4 (K := K) (ι := ι) hι
  have hpair23 := EightU.cubeRel_ctuEmbed_nsElt_zero φ4 (K := K) (ι := ι) hι
  have hm2 : nsElt (K := K) (2 : Fin 4) ∈ spBlock K ({0, 1} : Finset (Fin 4))ᶜ :=
    nsElt_mem_spBlock_compl_of_not_mem (by decide)
  have hm0 : nsElt (K := K) (0 : Fin 4) ∈ spBlock K ({2, 3} : Finset (Fin 4))ᶜ :=
    nsElt_mem_spBlock_compl_of_not_mem (by decide)
  have TB₀ := P₀.conj_t_eq_bar hset hK hF (by decide) hm2 (EightU.gElt_mem_ctuBlock φ4)
    hpair01.1 hpair01.2 ht hKt
  have TB₂ := P₂.conj_t_eq_bar hset hK hF (by decide) hm0 (EightU.gElt'_mem_ctuBlock φ4)
    hpair23.1 hpair23.2 ht hKt
  obtain ⟨a, ha⟩ : ∃ a : G, a = P₂.Φ ⟨EightU.tauElt φ4, ctuBlock_pair_le_left _ 2 3 hτ⟩ :=
    ⟨_, rfl⟩
  have hta := TB₂ (EightU.tauElt φ4) hτ
  have hkey : (⟨EightU.tauElt φ4, ctuBlock_pair_le_left _ 2 3 hτ⟩ :
      ctuBlock (unitaryInvolution F 2 1) 0 ({2} : Finset (Fin 4)))⁻¹ *
        ⟨barPow hσ true (EightU.tauElt φ4), ctuBlock_pair_le_left _ 2 3 hτb⟩ =
      ⟨ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι
        (permSp K (Equiv.swap (0 : Fin 4) 1)), ctuEmbed_mem_ctuBlock_iff.2 hw2⟩ :=
    Subtype.ext hτw
  have haw : a⁻¹ * t * a = ((e.symm (permSp K (Equiv.swap (0 : Fin 4) 1)) : L) : G) * t := by
    have h1 : a⁻¹ * t * a = a⁻¹ * (t * a * t⁻¹) * t := by group
    rw [h1, ha, hta, ← map_inv, ← map_mul, hkey, P₂.N1 _ hw2]
  have hwt : ∀ (y : SU (unitaryInvolution F 2 1) (2 * 4 + 0))
      (hy : y ∈ ctuBlock (unitaryInvolution F 2 1) 0 ({0, 1} : Finset (Fin 4))),
      (a⁻¹ * t * a) * P₀.Φ ⟨y, ctuBlock_pair_le_left _ 0 1 hy⟩ * (a⁻¹ * t * a)⁻¹ =
        P₀.Φ ⟨y, ctuBlock_pair_le_left _ 0 1 hy⟩ := by
    intro y hy
    have hyb : barPow hσ true y ∈ ctuBlock (unitaryInvolution F 2 1) 0 ({0, 1} : Finset (Fin 4)) :=
      (barPow_mem_ctuBlock_iff hσ true _ _).2 hy
    rw [haw]
    have h1 : (((e.symm (permSp K (Equiv.swap (0 : Fin 4) 1)) : L) : G) * t) *
        P₀.Φ ⟨y, ctuBlock_pair_le_left _ 0 1 hy⟩ *
          (((e.symm (permSp K (Equiv.swap (0 : Fin 4) 1)) : L) : G) * t)⁻¹ =
        ((e.symm (permSp K (Equiv.swap (0 : Fin 4) 1)) : L) : G) *
          (t * P₀.Φ ⟨y, ctuBlock_pair_le_left _ 0 1 hy⟩ * t⁻¹) *
            ((e.symm (permSp K (Equiv.swap (0 : Fin 4) 1)) : L) : G)⁻¹ := by group
    rw [h1, TB₀ y hy, hb _ hyb]
    congr 2
    exact barPow_true_barPow_true hσ y
  have hAperf := F4Pilot.commutator_centralizerPerfectCore
    (modelToG e (nsTorusSp K (0 : Fin 4) ⊔ nsTorusSp K 1))
  have hSperf : ⁅(centralizerPerfectCore (modelToG e (nsTorusSp K (0 : Fin 4) ⊔
      nsTorusSp K 1))).map (MulAut.conj a).toMonoidHom,
      (centralizerPerfectCore (modelToG e (nsTorusSp K (0 : Fin 4) ⊔
        nsTorusSp K 1))).map (MulAut.conj a).toMonoidHom⁆ =
      (centralizerPerfectCore (modelToG e (nsTorusSp K (0 : Fin 4) ⊔
        nsTorusSp K 1))).map (MulAut.conj a).toMonoidHom := by
    rw [← map_commutator, hAperf]
  have hSt : (centralizerPerfectCore (modelToG e (nsTorusSp K (0 : Fin 4) ⊔
      nsTorusSp K 1))).map (MulAut.conj a).toMonoidHom ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨y, hy, rfl⟩ := P₀.exists_eq_of_mem_overlap hF (by decide) hz
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have h1 := hwt y hy
    have h2 : a * P₀.Φ ⟨y, ctuBlock_pair_le_left _ 0 1 hy⟩ * a⁻¹ * t =
        a * ((a⁻¹ * t * a) * P₀.Φ ⟨y, ctuBlock_pair_le_left _ 0 1 hy⟩ * (a⁻¹ * t * a)⁻¹) *
          a⁻¹ * t := by
      rw [h1]
    rw [h2]
    group
  have hSL := std_perfect_le hset.standardSetting hOut htC ht hSperf hSt
  have haX : a * ((e.symm (nsElt 2) : L) : G) = ((e.symm (nsElt 2) : L) : G) * a := by
    have hamem : a ∈ centralizerPerfectCore (modelToG e (nsTorusSp K (2 : Fin 4))) := by
      rw [← P₂.range_eq, ha]
      exact ⟨_, rfl⟩
    have h1 := F4Pilot.centralizerPerfectCore_le_centralizer _ hamem
    exact (mem_centralizer_iff.1 h1 _ (UnitaryPilot.symm_mem_modelToG e
      (nsElt_mem_nsTorusSp (2 : Fin 4)))).symm
  exact P₀.false_of_overlap_conj_le hK hF (by decide) hm2 (EightU.gElt_mem_ctuBlock φ4)
    hpair01.1 hpair01.2 haX fun y hy => hSL ⟨_, P₀.mem_overlap hF (by decide) hy, rfl⟩

end Key

end CFSG.SeitzReduction.SymplecticPilot
