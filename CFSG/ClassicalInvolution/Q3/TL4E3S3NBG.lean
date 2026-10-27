module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3NB
public import CFSG.ClassicalInvolution.Q3.TL4E3S3GenDefs
public import CFSG.ClassicalInvolution.Q3.TL4E3S3ZB
public import CFSG.ClassicalInvolution.Q3.TL4MF163M12A
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4All

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.Blueprint

namespace E3S3NBG

theorem mul_self_mem_of_index_dvd_six {G : Type} [Group G] [Finite G] {N : Subgroup G} [N.Normal]
    (h6 : N.index ∣ 6) {g : G} (hg : g ^ 4 = 1) : g * g ∈ N := by
  set π := QuotientGroup.mk' N with hπ
  have h1 : orderOf (π g) ∣ 4 := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hg, map_one])
  have h2 : orderOf (π g) ∣ 6 := (orderOf_dvd_natCard (π g)).trans h6
  have h3 : orderOf (π g) ∣ 2 := by
    have := Nat.dvd_gcd h1 h2
    norm_num at this
    exact this
  have h4 : π (g * g) = 1 := by
    rw [map_mul, ← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp h3
  exact (QuotientGroup.eq_one_iff (g * g)).mp h4

variable {Y : Type} [Group Y]

theorem centralizer_mk_le_map {a : Y}
    (ha : ∀ y : Y, ∀ c ∈ Subgroup.center Y, y * a * y⁻¹ = a * c → c = 1) :
    Subgroup.centralizer ({QuotientGroup.mk' (Subgroup.center Y) a} :
        Set (Y ⧸ Subgroup.center Y)) ≤
      (Subgroup.centralizer ({a} : Set Y)).map (QuotientGroup.mk' (Subgroup.center Y)) := by
  intro yb hyb
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center Y) yb
  rw [Subgroup.mem_centralizer_singleton_iff] at hyb
  have hc : a⁻¹ * (y * a * y⁻¹) ∈ Subgroup.center Y := by
    rw [← QuotientGroup.eq]
    show QuotientGroup.mk' (Subgroup.center Y) a =
      QuotientGroup.mk' (Subgroup.center Y) (y * a * y⁻¹)
    rw [map_mul, map_mul, map_inv, hyb]
    group
  have h1 := ha y _ hc (by group)
  have h2 : y * a * y⁻¹ = a := by
    calc y * a * y⁻¹ = a * (a⁻¹ * (y * a * y⁻¹)) := by group
      _ = a := by rw [h1, mul_one]
  refine ⟨y, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  calc y * a = y * a * y⁻¹ * y := by group
    _ = a * y := by rw [h2]

section Exit


variable [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem sup_centralizer_of_edgeless_exit {n : ℕ} (hL2 : E3C269L2) (hL3 : E3S3GenL3)
    (hU3 : E3S3GenU3) (hM12 : E3S3GenM12) (hA : ModelM12Acts3) (hE4 : SecIdE4Edge)
    (h6 : Thm6RBelow 3 n) (hY : Nat.card Y < n) (hd : TightDatum R S t) (hc : TightCls Y R S t)
    {S' : Sylow 2 R} (hex : TightEx Y R S' t) (hE : TightEdgeless R) (hE2 : ¬ TightInO2 t)
    {s : Y} (hts : t * s = s * t) (hst : s ≠ t) (hconj : ∃ g : Y, s = g * t * g⁻¹) :
    Subgroup.centralizer ({t} : Set Y) ⊔ Subgroup.centralizer ({s} : Set Y) = ⊤ := by
  classical
  set Z := Subgroup.center Y with hZdef
  set π := QuotientGroup.mk' Z with hπdef
  have hN2 := E3S3Z.isPGroup_center hc
  have htN := E3S3Z.not_mem_center hc hE2
  have hnt := E3S3Z.noTwin hd hE
  obtain ⟨g₀, hg₀⟩ := hconj
  have hns : ∀ y : Y, ∀ c ∈ Z, y * s * y⁻¹ = s * c → c = 1 := by
    intro y c hcZ hy
    refine hnt (g₀⁻¹ * y * g₀) c hcZ ?_
    have hcc : g₀⁻¹ * c * g₀ = c := by
      rw [Subgroup.mem_center_iff.mp hcZ g₀⁻¹]
      group
    calc g₀⁻¹ * y * g₀ * t * (g₀⁻¹ * y * g₀)⁻¹ = g₀⁻¹ * (y * s * y⁻¹) * g₀ := by rw [hg₀]; group
      _ = g₀⁻¹ * (s * c) * g₀ := by rw [hy]
      _ = (g₀⁻¹ * s * g₀) * (g₀⁻¹ * c * g₀) := by group
      _ = t * c := by rw [hcc, hg₀]; group
  have ht2 : orderOf t = 2 := hd.order
  have htb2 : orderOf (π t) = 2 := by
    refine orderOf_eq_prime ?_ fun h => htN ((QuotientGroup.eq_one_iff t).mp h)
    rw [← map_pow, ← ht2, pow_orderOf_eq_one, map_one]
  have hsb2 : orderOf (π s) = 2 := by
    rw [hg₀, map_mul, map_mul, map_inv, ← MulAut.conj_apply, MulEquiv.orderOf_eq, htb2]
  have htsb : π t * π s = π s * π t := by rw [← map_mul, ← map_mul, hts]
  have hsZ : π s ≠ π t := by
    intro h
    apply hst
    have hcZ : t⁻¹ * s ∈ Z := by
      rw [← QuotientGroup.eq]
      exact h.symm
    have h1 := hnt g₀ _ hcZ (by rw [← hg₀]; group)
    calc s = t * (t⁻¹ * s) := by group
      _ = t := by rw [h1, mul_one]
  have hconjb : ∃ g : Y ⧸ Z, π s = g * π t * g⁻¹ :=
    ⟨π g₀, by rw [hg₀, map_mul, map_mul, map_inv]⟩
  suffices hgen : Subgroup.centralizer ({π t} : Set (Y ⧸ Z)) ⊔
      Subgroup.centralizer ({π s} : Set (Y ⧸ Z)) = ⊤ by
    rw [eq_top_iff]
    intro y _
    have hle : Subgroup.centralizer ({π t} : Set (Y ⧸ Z)) ⊔
        Subgroup.centralizer ({π s} : Set (Y ⧸ Z)) ≤
          (Subgroup.centralizer ({t} : Set Y) ⊔ Subgroup.centralizer ({s} : Set Y)).map π :=
      sup_le ((centralizer_mk_le_map hnt).trans (Subgroup.map_mono le_sup_left))
        ((centralizer_mk_le_map hns).trans (Subgroup.map_mono le_sup_right))
    obtain ⟨y', hy', hyy⟩ := hle (hgen ▸ Subgroup.mem_top (π y))
    have hcZ : y'⁻¹ * y ∈ Z := QuotientGroup.eq.mp hyy
    have hZt : Z ≤ Subgroup.centralizer ({t} : Set Y) := Subgroup.center_le_centralizer _
    have e : y = y' * (y'⁻¹ * y) := by group
    rw [e]
    exact Subgroup.mul_mem _ hy' (Subgroup.mem_sup_left (hZt hcZ))
  have hm := E3S3Z.edgelessMember3_quot hd hc hE2 hE
  rcases TightEx.reduce hd hc hex hE2 with ⟨-, h3⟩ | ⟨-, ⟨e⟩⟩ | ⟨hZ, h4⟩
  ·
    have hcb := TwistQ.cls hd le_rfl hN2 htN hc
    have hE2b : ¬ TightInO2 (π t) := fun h => hE2 (TwistQ.inO2_of hN2 h)
    have hZb := E3S3Z.center_quot_eq_bot hd hc hE2
    have h3b : ¬ TightActs3 (R.map π) (π t) :=
      fun h => h3 (E3S3Z.acts3_of_map hd le_rfl hN2 htN hnt h)
    have hq : TightFStarQuasisimple (Y ⧸ Z) := by
      rcases tightDichotomy_of hm.datum hcb with h | h | ⟨L, -, -, -, -, -, hFc, hFL⟩
      · exact absurd h hE2b
      · exact h
      · rw [hZb] at hFc
        exact absurd (hFc.trans bot_le) hFL
    have hZF : Subgroup.center ↥(genFittingFStar (Y ⧸ Z)) = ⊥ := by
      have h1 := TightDatum.center_genFittingFStar_le hm.datum hcb hE2b
      rw [hZb, le_bot_iff] at h1
      exact (Subgroup.map_eq_bot_iff_of_injective _ (genFittingFStar _).subtype_injective).mp h1
    obtain ⟨hs, -⟩ := isSimpleGroup_of_quasisimple_of_center_eq_bot hq hZF
    have hlt : Nat.card (Y ⧸ Z) < n :=
      lt_of_le_of_lt (Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)) hY
    obtain ⟨ι, hι, -, hιz⟩ := MF163.exists_quat_of_member hm
    have hq4 : ∀ q : QuaternionGroup 2, q ^ 4 = 1 := by decide
    have ha2 : (QuaternionGroup.a 2 : QuaternionGroup 2) =
        QuaternionGroup.a 1 * QuaternionGroup.a 1 := by decide
    have hFn : (genFittingFStar (Y ⧸ Z)).Normal := genFittingFStar_normal _
    have hsF : π t ∈ genFittingFStar (Y ⧸ Z) → π s ∈ genFittingFStar (Y ⧸ Z) := fun htF => by
      rw [hg₀, map_mul, map_mul, map_inv]
      exact hFn.conj_mem _ htF _
    rcases h6 _ hlt _ _ _ hm.datum hm.cls hE2b hq hm.edgeless with hg | hX
    · exact absurd (acts3_of_good (TwistQ.good_of hd le_rfl hN2 htN hnt hg)) h3
    · have := hs
      obtain ⟨p, f, hp, hp2, ⟨hf, hl, hi⟩ | ⟨hl | hl, hi6⟩⟩ | ⟨hm12, hi⟩ := hX
      · refine hL2 _ hs hi p f hp hp2 hf hl ι hι (π t) (π s) hιz ?_ htsb hsZ hconjb
        rw [← hιz, ha2, map_mul]
        exact E3C269G.mul_self_mem_of_index_le_two hi _
      · have htF : π t ∈ genFittingFStar (Y ⧸ Z) := by
          rw [← hιz, ha2, map_mul]
          exact mul_self_mem_of_index_dvd_six hi6 (by rw [← map_pow, hq4, map_one])
        exact hL3 _ hs p f hp hp2 hl (π t) (π s) htb2 hsb2 htF (hsF htF) htsb hsZ
      · have htF : π t ∈ genFittingFStar (Y ⧸ Z) := by
          rw [← hιz, ha2, map_mul]
          exact mul_self_mem_of_index_dvd_six hi6 (by rw [← map_pow, hq4, map_one])
        exact hU3 _ hs p f hp hp2 hl (π t) (π s) htb2 hsb2 htF (hsF htF) htsb hsZ
      · exact absurd (hA _ _ _ _ hm hs hi hm12) h3b
  ·
    exact hM12 _ ⟨e⟩ (π t) (π s) htb2 htsb hsZ hconjb
  ·
    exact absurd hE (hE4 _ _ _ _ hd hc hE2 hZ h4)

end Exit

end E3S3NBG

section E4


variable {n : ℕ}

theorem tightSecGenS3_of_facts (hL2 : E3C269L2) (hL3 : E3S3GenL3) (hU3 : E3S3GenU3)
    (hM12 : E3S3GenM12) (hA : ModelM12Acts3) (hE4 : SecIdE4Edge) : TightSecGenS3 n := by
  intro Y _ _ R S t J u hF htu ht Sb hex hedge hnE2 s hts hst hconj
  obtain ⟨Sq, hd, hc⟩ := hF.exists_secCls htu ht
  exact E3S3NBG.sup_centralizer_of_edgeless_exit hL2 hL3 hU3 hM12 hA hE4 hF.plus.thm6
    hF.card_secQ_lt hd hc hex hedge hnE2 hts hst hconj

end E4

section Cit3M


variable {n : ℕ}

theorem tightSecGenS3_of (hL2 : E3C269L2) (hL3 : E3S3GenL3) (hU3 : E3S3GenU3)
    (hM12 : E3S3GenM12) : TightSecGenS3 n :=
  tightSecGenS3_of_facts hL2 hL3 hU3 hM12 modelM12Acts3_proved secIdE4Edge_proved

theorem tightE3S3NotBeta_of_facts (hL2 : E3C269L2) (hL3 : E3S3GenL3) (hU3 : E3S3GenU3)
    (hM12 : E3S3GenM12) : TightE3S3NotBeta n :=
  tightE3S3NotBeta_of_gen (tightSecGenS3_of hL2 hL3 hU3 hM12)

end Cit3M

end CFSG.ClassicalInvolution.Q3.TL4
