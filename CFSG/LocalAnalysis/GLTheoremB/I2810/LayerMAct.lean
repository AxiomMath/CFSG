module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Defs
public import CFSG.CGT.T75N.A9Weak

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.LayerM

namespace ActAux

open CFSG.Quasithin CFSG.SectionRank.Ccomm
open CFSG.CGT.T75N (c5 c5_pow c5_ne a9Input_weak)

theorem exists_quotAct {W : Type} [CommGroup W] (h2 : ∀ v : W, v * v = 1)
    (X : Subgroup (MulAut W)) (C : Subgroup W) (hfix : ∀ g ∈ X, ∀ c ∈ C, g c = c) :
    ∃ ρ : ↥X →* MulAut (W ⧸ C),
      (∀ (g : ↥X) (v : W), ρ g (QuotientGroup.mk v) = QuotientGroup.mk ((g : MulAut W) v)) ∧
        ∀ g : ↥X, ρ g = 1 → g * g = 1 := by
  have hXle : X ≤ stabSub C := by
    intro g hg u
    constructor
    · intro h
      have hu : g u = u := g.injective (hfix g hg _ h)
      rw [hu] at h
      exact h
    · intro h
      rw [hfix g hg u h]
      exact h
  refine ⟨(quotHom C).comp (Subgroup.inclusion hXle), fun g v => rfl, fun g hg => ?_⟩
  have hall : ∀ v : W, (g : MulAut W) v * v⁻¹ ∈ C := by
    intro v
    have h1 : (QuotientGroup.mk ((g : MulAut W) v) : W ⧸ C) = QuotientGroup.mk v :=
      congrArg (fun φ : MulAut (W ⧸ C) => φ (QuotientGroup.mk v)) hg
    exact (mk_eq_mk_iff _ _).1 h1
  have hsq : ∀ v : W, (g : MulAut W) ((g : MulAut W) v) = v := by
    intro v
    obtain ⟨c, hc⟩ : ∃ c : W, c = (g : MulAut W) v * v⁻¹ := ⟨_, rfl⟩
    have hcC : c ∈ C := hc ▸ hall v
    have hgv : (g : MulAut W) v = c * v := by rw [hc]; exact (inv_mul_cancel_right _ _).symm
    calc (g : MulAut W) ((g : MulAut W) v) = (g : MulAut W) (c * v) := by rw [← hgv]
      _ = c * (c * v) := by rw [map_mul, hfix g g.2 c hcC, hgv]
      _ = (c * c) * v := (mul_assoc _ _ _).symm
      _ = v := by rw [h2 c, one_mul]
  exact Subtype.ext (MulEquiv.ext fun v => hsq v)

theorem quot_mul_self {W : Type} [CommGroup W] (h2 : ∀ v : W, v * v = 1) (C : Subgroup W) :
    ∀ x : W ⧸ C, x * x = 1 := by
  intro x
  induction x using QuotientGroup.induction_on with
  | H v => rw [← QuotientGroup.mk_mul, h2 v]; rfl

theorem card_mulAut_elementary {N : Type} [Group N] [Finite N] (hc : ∀ a b : N, a * b = b * a)
    (h2 : ∀ a : N, a * a = 1) :
    ∃ e : ℕ, Nat.card N = 2 ^ e ∧ Nat.card (MulAut N) = ∏ i : Fin e, (2 ^ e - 2 ^ (i : ℕ)) := by
  have hp : IsPGroup 2 N := fun x => ⟨1, by rw [pow_one, pow_two]; exact h2 x⟩
  obtain ⟨e, he⟩ := hp.exists_card_eq
  obtain ⟨φ⟩ := nonempty_mulEquiv_of_elementary (p := 2) hc
    (fun a => by rw [pow_two]; exact h2 a) he
  exact ⟨e, he, by rw [card_mulAut_eq_card_GL φ, card_GL_zmod]⟩

theorem card_alt7 : Nat.card ↥(alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem prod_gl_four : ∏ i : Fin 4, (2 ^ 4 - 2 ^ (i : ℕ)) = 20160 := by
  simp [Fin.prod_univ_succ]

theorem not_dvd_prod_gl {e : ℕ} (he : e ≤ 3) : ¬ 2520 ∣ ∏ i : Fin e, (2 ^ e - 2 ^ (i : ℕ)) := by
  interval_cases e <;> simp [Fin.prod_univ_succ]

theorem c5_mul_self_ne : c5 * c5 ≠ 1 := by
  intro h
  have h5 : c5 ^ 5 = c5 := by
    calc c5 ^ 5 = (c5 * c5) * (c5 * c5) * c5 := by simp [pow_succ, mul_assoc]
      _ = c5 := by rw [h]; simp
  exact c5_ne (h5.symm.trans c5_pow)

variable {V : Type} [Group V] [Finite V]
variable {Kh Eh : Subgroup (MulAut V)}

theorem kh_embeds {n : ℕ} {π : ↥Kh →* ↥(alternatingGroup (Fin n))}
    {Vv V₄ : Subgroup ↥(alternatingGroup (Fin n))} (hc : ∀ a b : V, a * b = b * a)
    (h2 : ∀ v : V, v * v = 1) (d : ASData Kh Eh n π Vv V₄) :
    ∃ e : ℕ, (fixV' Kh).index = 2 ^ e ∧ Nat.card ↥Kh ∣ ∏ i : Fin e, (2 ^ e - 2 ^ (i : ℕ)) := by
  letI : CommGroup V := { ‹Group V› with mul_comm := hc }
  obtain ⟨ρ, -, hρ⟩ := exists_quotAct h2 Kh (fixV' Kh) fun g hg c hc' => hc' g hg
  have hp : IsPGroup 2 ρ.ker := fun x => ⟨1, by
    rw [pow_one, pow_two]
    exact Subtype.ext (by simpa using hρ x.1 x.2)⟩
  have hle : ρ.ker ≤ CFSG.pCore 2 ↥Kh := le_sSup ⟨ρ.normal_ker, hp⟩
  have hinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← d.o2]
    exact hle
  obtain ⟨e, he, hGL⟩ := card_mulAut_elementary (fun a b => mul_comm a b)
    (quot_mul_self h2 (fixV' Kh))
  refine ⟨e, ?_, ?_⟩
  · rw [Subgroup.index, he]
  · rw [← hGL]
    exact Subgroup.card_dvd_of_injective ρ hinj

theorem card_kh_eq {π7 : ↥Kh →* ↥(alternatingGroup (Fin 7))}
    {Vv7 V₇ : Subgroup ↥(alternatingGroup (Fin 7))} (d : ASData Kh Eh 7 π7 Vv7 V₇) :
    Nat.card ↥Kh = Nat.card ↥(Subgroup.center ↥Kh) * 2520 := by
  have h := Subgroup.card_ker_mul_card_of_surjective d.surj
  rw [d.ker, card_alt7] at h
  exact h.symm

end ActAux

open ActAux
open CFSG.CGT.T75N (c5 a9Input_weak)

variable {V : Type} [Group V] [Finite V]
variable {Kh Eh : Subgroup (MulAut V)}

theorem a9_exclusion_aux (hc : ∀ a b : V, a * b = b * a) (h2 : ∀ v : V, v * v = 1)
    {J Y : Subgroup (MulAut V)}
    (hJ : (fixV' J).index ≤ 2 ^ 6) (hYJ : Y ≤ J) (π' : ↥Y →* ↥(alternatingGroup (Fin 9)))
    (hπ : Function.Surjective π') (hker : π'.ker ≤ Subgroup.center ↥Y) : False := by
  letI : CommGroup V := { ‹Group V› with mul_comm := hc }
  obtain ⟨ρ, -, hρ⟩ := exists_quotAct h2 Y (fixV' J) fun g hg c hc' => hc' g (hYJ hg)
  have hK : ρ.ker ≤ π'.ker := by
    have : IsSimpleGroup ↥(alternatingGroup (Fin 9)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
    haveI : (ρ.ker.map π').Normal := Subgroup.Normal.map ρ.normal_ker π' hπ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ρ.ker.map π') with h | h
    · intro k hk
      have h1 : π' k ∈ (⊥ : Subgroup ↥(alternatingGroup (Fin 9))) :=
        h ▸ Subgroup.mem_map_of_mem π' hk
      exact Subgroup.mem_bot.1 h1
    · obtain ⟨k, hk, hkc⟩ : c5 ∈ ρ.ker.map π' := h ▸ Subgroup.mem_top _
      exact absurd (by rw [← hkc, ← map_mul, hρ k hk, map_one]) c5_mul_self_ne
  have hlt := a9Input_weak ↥Y π'.ker hker ⟨QuotientGroup.quotientKerEquivOfSurjective π' hπ⟩
    (V ⧸ fixV' J) (fun a b => mul_comm a b) (quot_mul_self h2 (fixV' J)) ρ hK
  have hidx : (fixV' J).index = Nat.card (V ⧸ fixV' J) := rfl
  omega

theorem a7_small_false_aux (hc : ∀ a b : V, a * b = b * a) (h2 : ∀ v : V, v * v = 1)
    {π7 : ↥Kh →* ↥(alternatingGroup (Fin 7))} {Vv7 V₇ : Subgroup ↥(alternatingGroup (Fin 7))}
    (d : ASData Kh Eh 7 π7 Vv7 V₇) (hidx : (fixV' Kh).index ≤ 8) : False := by
  obtain ⟨e, he, hdvd⟩ := kh_embeds hc h2 d
  have he3 : e ≤ 3 := by
    have h : 2 ^ e ≤ 2 ^ 3 := he ▸ hidx
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h
  exact not_dvd_prod_gl he3 ((Dvd.intro_left _ (card_kh_eq d).symm).trans hdvd)

theorem a7_center_index_aux (hc : ∀ a b : V, a * b = b * a) (h2 : ∀ v : V, v * v = 1)
    {π7 : ↥Kh →* ↥(alternatingGroup (Fin 7))} {Vv7 V₇ : Subgroup ↥(alternatingGroup (Fin 7))}
    (d : ASData Kh Eh 7 π7 Vv7 V₇) (hidx : (fixV' Kh).index ≤ 16) :
    Subgroup.center ↥Kh = ⊥ ∧ (fixV' Kh).index = 16 := by
  obtain ⟨e, he, hdvd⟩ := kh_embeds hc h2 d
  have hcard := card_kh_eq d
  have he4 : e ≤ 4 := by
    have h : 2 ^ e ≤ 2 ^ 4 := he ▸ hidx
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h
  have he4' : e = 4 := by
    by_contra hne
    exact not_dvd_prod_gl (by omega) ((Dvd.intro_left _ hcard.symm).trans hdvd)
  subst he4'
  refine ⟨?_, by rw [he]; norm_num⟩
  rw [prod_gl_four, hcard] at hdvd
  have hZ8 : Nat.card ↥(Subgroup.center ↥Kh) ∣ 2 ^ 3 := by
    have h : Nat.card ↥(Subgroup.center ↥Kh) * 2520 ∣ 8 * 2520 := by
      rw [show 8 * 2520 = 20160 by norm_num]
      exact hdvd
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hZ8
  have hp : IsPGroup 2 ↥(Subgroup.center ↥Kh) := IsPGroup.of_card hk
  have hle : Subgroup.center ↥Kh ≤ CFSG.pCore 2 ↥Kh := le_sSup ⟨inferInstance, hp⟩
  rw [d.o2] at hle
  exact le_bot_iff.1 hle

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.LayerM
