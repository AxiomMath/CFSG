module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HNSideFacts.F4Spec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HNSideFacts.F4Parts
public import CFSG.Sporadic.HNOddCore.FourPairComp
public import CFSG.Sporadic.Schreier.LyWords

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.HNRecog.SideF4

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native
  CFSG.ONSchreier CFSG.ONSchreier.Native Equiv

theorem prep_pword_hom {Γ : Type*} [Group Γ] {n j : ℕ} (f : Γ →* Perm (Fin n)) (g : ℕ → Γ)
    {S Sinv : Array (Array ℕ)} (hS : ∀ h < j, PRep n S[h]! (f (g h)))
    (hSinv : ∀ h < j, PRep n Sinv[h]! (f (g h))⁻¹) :
    ∀ (w : List ℤ), plettersOK j w = true →
      PRep n (pword n S Sinv w) (f (CFSG.Sporadic.LySchreier.evalWord g w))
  | [], _ => by
    simpa [pword, CFSG.Sporadic.LySchreier.evalWord_nil] using prep_pid (n := n)
  | l :: w, hw => by
    simp only [plettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hw
    obtain ⟨⟨hl0, hlj⟩, hw⟩ := hw
    have hw' : plettersOK j w = true := by
      simpa [plettersOK, List.all_eq_true] using hw
    have ih := prep_pword_hom f g hS hSinv w hw'
    have hlet := prep_pletter (gs := fun h => f (g h)) (j := j) (S := S) (Sinv := Sinv) hS hSinv
      ⟨hl0, hlj⟩
    rw [pword, CFSG.Sporadic.LySchreier.evalWord_cons, map_mul]
    have e : f (CFSG.Sporadic.LySchreier.letterVal g l) =
        if decide (0 < l) then f (g (l.natAbs - 1)) else (f (g (l.natAbs - 1)))⁻¹ := by
      unfold CFSG.Sporadic.LySchreier.letterVal
      by_cases hpos : 0 < l
      · rw [if_pos hpos, if_pos (decide_eq_true hpos)]
        congr 3
        omega
      · rw [if_neg hpos, if_neg (by simpa using hpos), map_inv]
        congr 3
        omega
    rw [e]
    exact prep_pcomp hlet ih

theorem plettersOK_mono {j k : ℕ} (hjk : j ≤ k) {w : List ℤ} (h : plettersOK j w = true) :
    plettersOK k w = true := by
  simp only [plettersOK, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at h ⊢
  exact fun l hl => ⟨(h l hl).1, (h l hl).2.trans hjk⟩

section Setup


abbrev CJ : Subgroup JH := Subgroup.centralizer {t4J}

@[expose] def t4G : CJ := ⟨t4J, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩

@[expose] def gJ (s : Fin 10) : CJ := ⟨g4 s, g4_mem s s.2⟩

@[expose] def gJn (s : ℕ) : CJ := if h : s < 10 then gJ ⟨s, h⟩ else 1

@[expose] def rhoJ : CJ →* Perm (Fin 800) := rho4.comp (C4J.subtype.comp cjHom)

theorem gJ_eq_gC4 (s : Fin 10) : C4J.subtype (cjHom (gJ s)) = gC4 ⟨s, by omega⟩ := by
  apply Subtype.ext
  show jR (g4 s) = gC s
  rw [gC, if_pos s.2]

theorem rhoJ_gJ (s : Fin 10) : rhoJ (gJ s) = rhoGen s := by
  rw [rhoJ, MonoidHom.comp_apply, MonoidHom.comp_apply, gJ_eq_gC4, rhoGen, dif_pos (by omega)]

theorem rhoJ_t4G : rhoJ t4G = 1 := by
  have h : C4J.subtype (cjHom t4G) = t4C := rfl
  rw [rhoJ, MonoidHom.comp_apply, MonoidHom.comp_apply, h]
  exact MonoidHom.mem_ker.1 t4C_mem_ker

theorem injective_cjSub : Function.Injective (fun x : CJ => C4J.subtype (cjHom x)) :=
  C4J.subtype_injective.comp cjHom_bijective.1

theorem t4G_central (y : CJ) : t4G * y = y * t4G :=
  Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 y.2).symm

theorem t4G_sq : t4G ^ 2 = 1 := by
  rw [pow_two]
  exact Subtype.ext t4J_sq

theorem t4G_ne_one : t4G ≠ 1 := fun h => t4J_ne_one (congrArg Subtype.val h)

theorem orderOf_t4G : orderOf t4G = 2 := orderOf_eq_prime t4G_sq t4G_ne_one

theorem ker_rhoJ : (rhoJ : CJ →* Perm (Fin 800)).ker = Subgroup.zpowers t4G := by
  ext x
  constructor
  · intro hx
    have h1 : C4J.subtype (cjHom x) ∈ rho4.ker := MonoidHom.mem_ker.2 hx
    rw [ker_rho4] at h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h1
    refine Subgroup.mem_zpowers_iff.2 ⟨k, injective_cjSub ?_⟩
    have h : C4J.subtype (cjHom t4G) = t4C := rfl
    show C4J.subtype (cjHom (t4G ^ k)) = C4J.subtype (cjHom x)
    rw [map_zpow, map_zpow, h]
    exact hk
  · intro hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [MonoidHom.mem_ker, map_zpow, rhoJ_t4G, one_zpow]

theorem card_ker_rhoJ : Nat.card (rhoJ : CJ →* Perm (Fin 800)).ker = 2 := by
  rw [ker_rhoJ, Nat.card_zpowers, orderOf_t4G]

theorem prep_rhoJ_gJn {h : ℕ} (hh : h < 10) : PRep 800 s800[h]! (rhoJ (gJn h)) := by
  rw [gJn, dif_pos hh, rhoJ_gJ]
  exact prep_rhoGen (by omega)

theorem prep_rhoJ_gJn_inv {h : ℕ} (hh : h < 10) :
    PRep 800 (pinvs 800 s800)[h]! (rhoJ (gJn h))⁻¹ := by
  rw [gJn, dif_pos hh, rhoJ_gJ]
  exact prep_rhoGen_inv (by omega)

theorem prep_rhoJ_word {w : List ℤ} (hw : plettersOK 10 w = true) :
    PRep 800 (pword 800 s800 (pinvs 800 s800) w)
      (rhoJ (CFSG.Sporadic.LySchreier.evalWord gJn w)) :=
  prep_pword_hom rhoJ gJn (fun h hh => prep_rhoJ_gJn hh) (fun h hh => prep_rhoJ_gJn_inv hh) w hw

theorem qbar_mem_rhoJ_range {i : ℕ} (hi : i < 8) :
    qbar i ∈ (rhoJ : CJ →* Perm (Fin 800)).range := by
  obtain ⟨-, -, -, h⟩ := sideF4QOK_parts sideF4QOK_true
  obtain ⟨hl, hp⟩ := h i hi
  have h2 := prep_of_peq_left hp (prep_rhoJ_word hl)
  exact ⟨_, (permOfArr_eq_of_prep h2).symm⟩

theorem Qbar_le_rhoJ_range : Qbar ≤ (rhoJ : CJ →* Perm (Fin 800)).range := by
  rw [Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact qbar_mem_rhoJ_range i.2

abbrev QJ : Subgroup CJ := Qbar.comap rhoJ

theorem mem_QJ {x : CJ} : x ∈ QJ ↔ rhoJ x ∈ Qbar := Iff.rfl

theorem rhoJ_mem_range4 (x : CJ) : rhoJ x ∈ rho4.range :=
  MonoidHom.mem_range.2 ⟨C4J.subtype (cjHom x), rfl⟩

theorem t4G_mem_QJ : t4G ∈ QJ := by
  rw [mem_QJ, rhoJ_t4G]
  exact Qbar.one_mem

theorem QJ_normal : QJ.Normal := by
  refine ⟨fun n hn g => ?_⟩
  show rhoJ (g * n * g⁻¹) ∈ Qbar
  rw [map_mul, map_mul, map_inv]
  have h := Qbar_normal.conj_mem ⟨rhoJ n, rhoJ_mem_range4 n⟩ hn
    ⟨rhoJ g, rhoJ_mem_range4 g⟩
  exact h

instance QJ_normal_inst : QJ.Normal := QJ_normal

theorem card_QJ : Nat.card QJ = 512 := by
  have hK : (rhoJ : CJ →* Perm (Fin 800)).ker ≤ QJ := Subgroup.ker_le_comap _ _
  have h := card_ker_mul_card_map rhoJ hK
  rw [Subgroup.map_comap_eq, inf_eq_right.2 Qbar_le_rhoJ_range, card_Qbar, card_ker_rhoJ] at h
  omega

theorem centralizer_QJ_le : Subgroup.centralizer (QJ : Set CJ) ≤ QJ := by
  intro x hx
  rw [mem_QJ, ← centralizer_Qbar]
  refine ⟨Subgroup.mem_centralizer_iff.2 fun y hy => ?_, rhoJ_mem_range4 x⟩
  obtain ⟨q, hq⟩ := Qbar_le_rhoJ_range hy
  have hqQ : q ∈ QJ := by rw [mem_QJ, hq]; exact hy
  have := Subgroup.mem_centralizer_iff.1 hx q hqQ
  rw [← hq, ← map_mul, ← map_mul, this]

theorem commutator_mem_zpowers {x y : CJ} (hx : x ∈ QJ) (hy : y ∈ QJ) :
    x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers t4G := by
  rw [← ker_rhoJ, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
    Qbar_comm hx hy]
  simp

theorem sq_mem_zpowers {x : CJ} (hx : x ∈ QJ) : x ^ 2 ∈ Subgroup.zpowers t4G := by
  rw [← ker_rhoJ, MonoidHom.mem_ker, map_pow]
  exact Qbar_sq hx

end Setup

end CFSG.EvenSporadicStandard.HNRecog.SideF4
