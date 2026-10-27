module

public import CFSG.ClassicalInvolution.Q3.TL4VtxE4All
public import CFSG.ClassicalInvolution.Q3.TL4E3Norm
public import CFSG.ClassicalInvolution.Q3.TL4E3S3ZB
public import CFSG.ClassicalInvolution.Q3.TL4ExitDichX

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.SecEL

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open scoped MatrixGroups

section Quot

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem exists_conj_mem_sylow {G : Type} [Group G] [Finite G] (P : Sylow 2 G) {x : G} {k : ℕ}
    (hx : x ^ 2 ^ k = 1) : ∃ g : G, g * x * g⁻¹ ∈ (P : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 (Subgroup.zpowers x) := by
    rintro ⟨s, hs⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
    refine ⟨k, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  obtain ⟨Q, hQ⟩ := h2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  refine ⟨g, ?_⟩
  rw [← hg]
  exact ⟨x, hQ (Subgroup.mem_zpowers x), by simp [MulAut.conj_apply]⟩

theorem eq_one_of_quot_syl (hc : TightCls Y R S t) {γ : MulAut Y}
    (hγZ : ∀ x, QuotientGroup.mk' (Subgroup.center Y) (γ x) =
      QuotientGroup.mk' (Subgroup.center Y) x)
    (hγS : ∀ x ∈ (S : Subgroup R).map R.subtype, γ x = x) : γ = 1 := by
  refine E3S3Z.eq_one_of_quot hc hγZ fun x hx => ?_
  have hle : tightCore R ≤ γ.toMonoidHom.eqLocus (MonoidHom.id Y) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨hyR, hy2⟩
    obtain ⟨k, hk⟩ := hy2 ⟨y, Subgroup.mem_zpowers y⟩
    have hk' : (⟨y, hyR⟩ : R) ^ 2 ^ k = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val hk
      simpa using this
    obtain ⟨g, hg⟩ := exists_conj_mem_sylow S hk'
    set s : Y := ((g * ⟨y, hyR⟩ * g⁻¹ : R) : Y) with hs
    have hsS : s ∈ (S : Subgroup R).map R.subtype := ⟨_, hg, rfl⟩
    have hy : y = (g : Y)⁻¹ * s * (g : Y) := by
      rw [hs]
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      group
    have hm : (g : Y)⁻¹ * γ (g : Y) ∈ Subgroup.center Y := by
      rw [← QuotientGroup.eq]
      exact (hγZ g).symm
    have hmc : ∀ a : Y, a * ((g : Y)⁻¹ * γ (g : Y)) = ((g : Y)⁻¹ * γ (g : Y)) * a :=
      Subgroup.mem_center_iff.mp hm
    show γ y = y
    rw [hy, map_mul, map_mul, map_inv, hγS s hsS]
    have hγg : γ (g : Y) = (g : Y) * ((g : Y)⁻¹ * γ (g : Y)) := by group
    rw [hγg]
    set m := (g : Y)⁻¹ * γ (g : Y) with hmdef
    calc (g * m)⁻¹ * s * (g * m) = m⁻¹ * ((g : Y)⁻¹ * s * g) * m := by group
      _ = (g : Y)⁻¹ * s * g := by
        have h1 := hmc ((g : Y)⁻¹ * s * g)
        calc m⁻¹ * ((g : Y)⁻¹ * s * g) * m = m⁻¹ * (((g : Y)⁻¹ * s * g) * m) := by rw [mul_assoc]
          _ = m⁻¹ * (m * ((g : Y)⁻¹ * s * g)) := by rw [h1]
          _ = (g : Y)⁻¹ * s * g := by group
  exact hle hx

theorem concl163Syl_of_quot (hd : TightDatum R S t) (hc : TightCls Y R S t) (hE2 : ¬ TightInO2 t)
    (h : Concl163Syl (R.map (QuotientGroup.mk' (Subgroup.center Y)))
      (TwistQ.sylowMap (Subgroup.center Y) S) (QuotientGroup.mk' (Subgroup.center Y) t)) :
    Concl163Syl R S t := by
  set Z := Subgroup.center Y with hZdef
  intro β hβ2 hβS
  have hβZ : (Subgroup.center Y).map (β : Y →* Y) = Subgroup.center Y := Subgroup.map_center_eq β
  let βb : MulAut (Y ⧸ Z) := QuotientGroup.congr Z Z β hβZ
  have hβb : ∀ x : Y, βb (QuotientGroup.mk' Z x) = QuotientGroup.mk' Z (β x) :=
    fun x => QuotientGroup.congr_mk' Z Z β hβZ x
  have hβb2 : βb * βb = 1 := by
    ext xb
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Z xb
    rw [MulAut.mul_apply, hβb, hβb, ← MulAut.mul_apply, hβ2, MulAut.one_apply, MulAut.one_apply]
  have hβbS : ∀ xb ∈ ((TwistQ.sylowMap Z S : Subgroup _).map
      (R.map (QuotientGroup.mk' Z)).subtype), βb xb = xb := by
    rw [TwistQ.sylowMap_map_subtype]
    rintro _ ⟨x, hx, rfl⟩
    rw [hβb, hβS x hx]
  rcases h βb hβb2 hβbS with h1 | h1
  · left
    refine eq_one_of_quot_syl hc (fun x => ?_) hβS
    have h2 := DFunLike.congr_fun h1 (QuotientGroup.mk' Z x)
    rwa [hβb, MulAut.one_apply] at h2
  · right
    have hγ : (MulAut.conj t)⁻¹ * β = 1 := by
      refine eq_one_of_quot_syl hc (fun x => ?_) (fun x hx => ?_)
      · have h2 := DFunLike.congr_fun h1 (QuotientGroup.mk' Z x)
        rw [hβb, MulAut.conj_apply] at h2
        rw [MulAut.mul_apply, ← map_inv, MulAut.conj_apply, map_mul, map_mul, h2]
        simp only [map_inv]
        group
        rfl
      · have hxt : x * t = t * x :=
          Subgroup.mem_centralizer_singleton_iff.mp (hd.cent (Subgroup.map_subtype_le _ hx))
        rw [MulAut.mul_apply, hβS x hx, ← map_inv, MulAut.conj_apply]
        calc t⁻¹ * x * t⁻¹⁻¹ = t⁻¹ * (x * t) := by group
          _ = t⁻¹ * (t * x) := by rw [hxt]
          _ = x := by group
    calc β = MulAut.conj t * ((MulAut.conj t)⁻¹ * β) := by rw [mul_inv_cancel_left]
      _ = MulAut.conj t := by rw [hγ, mul_one]

end Quot

section Exits


variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem concl163Syl_of_e3a {n : ℕ} (h6 : Thm6RBelow 3 n) (hY : Nat.card Y < n)
    (hd : TightDatum R S t) (hc : TightCls Y R S t) (hE2 : ¬ TightInO2 t)
    (hE : TightEdgeless R) (h3 : ¬ TightActs3 R t) : Concl163Syl R S t := by
  have hN2 := E3S3Z.isPGroup_center hc
  have htN := E3S3Z.not_mem_center hc hE2
  have hnt := E3S3Z.noTwin hd hE
  have hm := E3S3Z.edgelessMember3_quot hd hc hE2 hE
  have hcb := TwistQ.cls hd le_rfl hN2 htN hc
  have hE2b : ¬ TightInO2 (QuotientGroup.mk' (Subgroup.center Y) t) :=
    fun h => hE2 (TwistQ.inO2_of hN2 h)
  have hZb := E3S3Z.center_quot_eq_bot hd hc hE2
  have h3b : ¬ TightActs3 (R.map (QuotientGroup.mk' (Subgroup.center Y)))
      (QuotientGroup.mk' (Subgroup.center Y) t) :=
    fun h => h3 (E3S3Z.acts3_of_map hd le_rfl hN2 htN hnt h)
  have hq : TightFStarQuasisimple (Y ⧸ Subgroup.center Y) := by
    rcases tightDichotomy_of hm.datum hcb with h | h | ⟨L, -, -, -, -, -, hFc, hFL⟩
    · exact absurd h hE2b
    · exact h
    · rw [hZb] at hFc
      exact absurd (hFc.trans bot_le) hFL
  have hZF : Subgroup.center ↥(genFittingFStar (Y ⧸ Subgroup.center Y)) = ⊥ := by
    have h1 := TightDatum.center_genFittingFStar_le hm.datum hcb hE2b
    rw [hZb, le_bot_iff] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ (genFittingFStar _).subtype_injective).mp h1
  obtain ⟨hs, hnab⟩ := isSimpleGroup_of_quasisimple_of_center_eq_bot hq hZF
  have hlt : Nat.card (Y ⧸ Subgroup.center Y) < n :=
    lt_of_le_of_lt (Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)) hY
  refine concl163Syl_of_quot hd hc hE2 ?_
  rcases h6 _ hlt _ _ _ hm.datum hm.cls hE2b hq hm.edgeless with hg | hX
  · exact absurd (acts3_of_good (TwistQ.good_of hd le_rfl hN2 htN hnt hg)) h3
  · have := hs
    obtain ⟨p, f, hp, hp2, ⟨hf, hl, hi⟩ | ⟨hl | hl, -⟩⟩ | ⟨hm12, hi⟩ := hX
    · obtain ⟨ι, hι, hιS, hιz⟩ := MF163.exists_quat_of_member_syl hm
      intro β hβ2 hβS
      have := MF163.eq_one_or_conj_of_quat_psl2 hp2 hl ι hι β hβ2 fun g => hβS _ (hιS g)
      rwa [hιz] at this
    · exact MF163.concl163Syl_of_exit hm (Or.inl h3b) (Or.inl ⟨p, f, hp, hp2, Or.inl hl⟩)
    · exact MF163.concl163Syl_of_exit hm (Or.inl h3b) (Or.inl ⟨p, f, hp, hp2, Or.inr hl⟩)
    · exact absurd (modelM12Acts3_proved _ _ _ _ hm hs hi hm12) h3b

theorem concl163Syl_of_edgeless_exit {n : ℕ} (h6 : Thm6RBelow 3 n) (hY : Nat.card Y < n)
    (hd : TightDatum R S t) (hc : TightCls Y R S t) {S' : Sylow 2 R} (hex : TightEx Y R S' t)
    (hE : TightEdgeless R) (hE2 : ¬ TightInO2 t) : Concl163Syl R S t := by
  rcases TightEx.reduce hd hc hex hE2 with ⟨-, h3⟩ | ⟨-, ⟨e⟩⟩ | ⟨hZ, h4⟩
  · exact concl163Syl_of_e3a h6 hY hd hc hE2 hE h3
  · exact concl163Syl_of_quot hd hc hE2
      (MF163.concl163Syl_m12 (E3S3Z.edgelessMember3_quot hd hc hE2 hE) ⟨e⟩)
  · exact absurd hE (secIdE4Edge_proved _ _ _ _ hd hc hE2 hZ h4)

end Exits

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.SecEL
