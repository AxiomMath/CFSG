module

public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoTwoSecTheta

public section

namespace CFSG.OddStandard.AltStdCycTwo.Two

open Subgroup Equiv Equiv.Perm AltStdBal AltStdSec

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ} {z u : G}

section Outcomes

theorem exists_partner_of_symOutcome (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    (hn : 9 ≤ n) {x : G} (hx : x ∈ centralizer ({z} : Set G))
    (hτ : (permOf T.toBase θ hx).IsSwap) (hx2 : x * x = 1) (hfus : ¬ IsConj z (z * x))
    (hzx : z ∈ centralizer ({x} : Set G))
    (hS : SymOutcome (QuotientGroup.mk (QuotientGroup.mk ⟨z, hzx⟩ : TwoSec x) : TwoSecO x)
      (n - 2)) :
    ∃ (b : G) (hb : b ∈ centralizer ({z} : Set G)), IsConj z b ∧ b ≠ z ∧
      ((fixFin (permOf T.toBase θ hb)).card = n - 2 ∨
        (fixFin (permOf T.toBase θ hb)).card = n - 4) := by
  classical
  obtain ⟨y, hy, hxy⟩ := exists_oddY_conj_swapIota T θ hx hx2
  have hz2 : z * z = 1 := T.cyc.mul_self
  obtain ⟨ε, hε⟩ := hS
  have hzb2 : (QuotientGroup.mk ⟨z, hzx⟩ : TwoSec x) * QuotientGroup.mk ⟨z, hzx⟩ = 1 := by
    rw [← QuotientGroup.mk_mul]
    have : (⟨z, hzx⟩ : ↥(centralizer ({x} : Set G))) * ⟨z, hzx⟩ = 1 := Subtype.ext hz2
    rw [this]
    rfl
  have hzbb2 : (QuotientGroup.mk (QuotientGroup.mk ⟨z, hzx⟩ : TwoSec x) : TwoSecO x) *
      QuotientGroup.mk (QuotientGroup.mk ⟨z, hzx⟩ : TwoSec x) = 1 := by
    rw [← QuotientGroup.mk_mul, hzb2]
    rfl
  have hFcard : (fixFin (permOf T.toBase θ hx)).card = n - 2 := card_fixFin_of_isSwap hτ
  set Ψ : Perm ↥(fixFin (permOf T.toBase θ hx)) →* Perm (Fin (n - 2 + 2)) :=
    ε.symm.toMonoidHom.comp (twoThetaO T θ hx hxy) with hΨ
  have hinj : Function.Injective Ψ :=
    ε.symm.injective.comp (twoThetaO_injective T θ (by omega) hx hτ hx2 hy hxy)
  have hcomm : ∀ π, Ψ π * ε.symm (QuotientGroup.mk (QuotientGroup.mk ⟨z, hzx⟩ : TwoSec x)) =
      ε.symm (QuotientGroup.mk (QuotientGroup.mk ⟨z, hzx⟩ : TwoSec x)) * Ψ π := by
    intro π
    simp only [hΨ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, twoThetaO_comm T θ hx hy hxy hzx π]
  have hneΨ : ∀ π, Ψ π ≠ ε.symm (QuotientGroup.mk (QuotientGroup.mk ⟨z, hzx⟩ : TwoSec x)) := by
    intro π hπ
    simp only [hΨ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom] at hπ
    exact twoThetaO_ne T θ (by omega) hx hτ hx2 hy hxy hzx π (ε.symm.injective hπ)
  obtain ⟨i, hi, j, hj, hij⟩ :=
    Finset.one_lt_card.1 (show 1 < (fixFin (permOf T.toBase θ hx)).card by omega)
  set σ₀ : Perm ↥(fixFin (permOf T.toBase θ hx)) := swap ⟨i, hi⟩ ⟨j, hj⟩ with hσ₀
  have hσ₀s : σ₀.IsSwap := ⟨⟨i, hi⟩, ⟨j, hj⟩, fun h' => hij (congrArg Subtype.val h'), rfl⟩
  obtain ⟨τ', hτ's, -, hτ'ne, hΨσ⟩ := embedding_swap_cases
    (α := ↥(fixFin (permOf T.toBase θ hx))) (β := Fin (n - 2 + 2))
    (by simp only [Fintype.card_fin, Fintype.card_coe]; omega)
    (by simp only [Fintype.card_coe]; omega) Ψ hinj hε hcomm hneΨ hσ₀s
  obtain ⟨p₀, q₀, hpq₀, hτ₀e⟩ := hε
  obtain ⟨r₀, s₀, hrs₀, hτ'e⟩ := hτ's
  obtain ⟨c, hc⟩ := isConj_iff.1 (Equiv.Perm.isConj_swap hpq₀ hrs₀)
  have hετ' : ε τ' =
      ε c * QuotientGroup.mk (QuotientGroup.mk ⟨z, hzx⟩ : TwoSec x) * (ε c)⁻¹ := by
    rw [hτ'e, ← hc, ← hτ₀e, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hk₀C := twoKappa_mem_centralizer T θ hx hy hxy σ₀
  have hk₀z := twoKappa_comm_z T θ hx hy hxy σ₀
  have hpk₀ := permOf_twoKappa T θ hx hy hxy σ₀
  have hk₀2 : twoKappa T θ hx hxy σ₀ * twoKappa T θ hx hxy σ₀ = 1 := by
    rw [← map_mul, hσ₀, swap_mul_self, map_one]
  obtain ⟨s, hs2, hsmk, hsz, hsC, hps⟩ : ∃ s : ↥(centralizer ({x} : Set G)), s * s = 1 ∧
      (QuotientGroup.mk (QuotientGroup.mk s : TwoSec x) : TwoSecO x) = ε τ' ∧
      (s : G) * z = z * s ∧ ∃ hsC : (s : G) ∈ centralizer ({z} : Set G),
        permOf T.toBase θ hsC = Perm.ofSubtype σ₀ := by
    rcases hΨσ with h1 | h1
    · refine ⟨twoKappa T θ hx hxy σ₀, hk₀2, ?_, hk₀z, hk₀C, hpk₀⟩
      have h2 : ε (Ψ σ₀) = ε τ' := by rw [h1]
      simp only [hΨ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.apply_symm_apply] at h2
      rw [← h2, twoThetaO_apply]
    · have hzC : z ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 rfl
      have hk : twoKappa T θ hx hxy σ₀ * ⟨z, hzx⟩ = ⟨z, hzx⟩ * twoKappa T θ hx hxy σ₀ :=
        Subtype.ext hk₀z
      have hZ : (⟨z, hzx⟩ : ↥(centralizer ({x} : Set G))) * ⟨z, hzx⟩ = 1 := Subtype.ext hz2
      refine ⟨⟨z, hzx⟩ * twoKappa T θ hx hxy σ₀, ?_, ?_, ?_, mul_mem hzC hk₀C, ?_⟩
      · calc (⟨z, hzx⟩ : ↥(centralizer ({x} : Set G))) * twoKappa T θ hx hxy σ₀ *
              (⟨z, hzx⟩ * twoKappa T θ hx hxy σ₀)
            = ⟨z, hzx⟩ * (twoKappa T θ hx hxy σ₀ * ⟨z, hzx⟩) * twoKappa T θ hx hxy σ₀ := by
              group
          _ = ⟨z, hzx⟩ * (⟨z, hzx⟩ * twoKappa T θ hx hxy σ₀) * twoKappa T θ hx hxy σ₀ := by
              rw [hk]
          _ = (⟨z, hzx⟩ * ⟨z, hzx⟩) *
              (twoKappa T θ hx hxy σ₀ * twoKappa T θ hx hxy σ₀) := by group
          _ = 1 := by rw [hZ, hk₀2, one_mul]
      · have h2 : ε (Ψ σ₀) =
            ε (ε.symm (QuotientGroup.mk (QuotientGroup.mk ⟨z, hzx⟩ : TwoSec x)) * τ') := by
          rw [h1]
        simp only [hΨ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
          MulEquiv.apply_symm_apply, map_mul] at h2
        have h3 : (QuotientGroup.mk (QuotientGroup.mk (⟨z, hzx⟩ * twoKappa T θ hx hxy σ₀ :
            ↥(centralizer ({x} : Set G))) : TwoSec x) : TwoSecO x) =
            QuotientGroup.mk (QuotientGroup.mk ⟨z, hzx⟩ : TwoSec x) *
              twoThetaO T θ hx hxy σ₀ := by
          rw [twoThetaO_apply, QuotientGroup.mk_mul, QuotientGroup.mk_mul]
        rw [h3, h2, ← mul_assoc, hzbb2, one_mul]
      · show z * (twoKappa T θ hx hxy σ₀ : G) * z = z * (z * twoKappa T θ hx hxy σ₀)
        rw [mul_assoc, hk₀z]
      · rw [permOf_mul T.toBase θ hzC hk₀C (mul_mem hzC hk₀C),
          (permOf_eq_one_iff T.toBase θ hzC).2 (T.cyc.le T.cyc.mem), one_mul, hpk₀]
  have hs2' : (QuotientGroup.mk s : TwoSec x) * QuotientGroup.mk s = 1 := by
    rw [← QuotientGroup.mk_mul, hs2]
    rfl
  obtain ⟨wb, hwb⟩ := exists_conj_of_mk_conj_oddCore hzb2 hs2' (k := ε c) (by rw [hsmk, hετ'])
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective wb
  set b₀ : ↥(centralizer ({x} : Set G)) := w * ⟨z, hzx⟩ * w⁻¹ with hb₀
  have hmkb : (QuotientGroup.mk b₀ : TwoSec x) = QuotientGroup.mk s := by
    rw [hb₀, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact hwb
  set b : G := (b₀ : G) with hbdef
  have hbx : b ∈ centralizer ({x} : Set G) := b₀.2
  have hmkb' : (QuotientGroup.mk ⟨b, hbx⟩ : TwoSec x) = QuotientGroup.mk s := hmkb
  have hb : b ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    refine comm_of_mk_comm hx2 hfus hzx hbx ?_
    rw [hmkb', ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext hsz
  have hbs : b = (s : G) ∨ b = (s : G) * x := by
    have h2 := (mem_zpowers_selfC_iff hx2).1 (QuotientGroup.eq.1 hmkb'.symm)
    rcases h2 with h2 | h2
    · left
      have h2' : (s : G)⁻¹ * b = 1 := by simpa using h2
      exact (inv_mul_eq_one.1 h2').symm
    · right
      have h2' : (s : G)⁻¹ * b = x := by simpa using h2
      calc b = (s : G) * ((s : G)⁻¹ * b) := by group
        _ = (s : G) * x := by rw [h2']
  have hσ' : (Perm.ofSubtype σ₀).IsSwap := hσ₀s.of_subtype_isSwap
  have hcard : (fixFin (permOf T.toBase θ hb)).card = n - 2 ∨
      (fixFin (permOf T.toBase θ hb)).card = n - 4 := by
    rcases hbs with h1 | h1
    · left
      have hpb : permOf T.toBase θ hb = Perm.ofSubtype σ₀ :=
        (permOf_congr T.toBase θ h1 hb hsC).trans hps
      rw [hpb]
      exact card_fixFin_of_isSwap hσ'
    · right
      have hsxC : (s : G) * x ∈ centralizer ({z} : Set G) := mul_mem hsC hx
      have hpb : permOf T.toBase θ hb = Perm.ofSubtype σ₀ * permOf T.toBase θ hx :=
        (permOf_congr T.toBase θ h1 hb hsxC).trans
          (by rw [permOf_mul T.toBase θ hsC hx hsxC, hps])
      have hd : (Perm.ofSubtype σ₀).Disjoint (permOf T.toBase θ hx) := by
        intro i
        by_cases hi : i ∈ fixFin (permOf T.toBase θ hx)
        · exact Or.inr (mem_fixFin.1 hi)
        · exact Or.inl (Perm.ofSubtype_apply_of_not_mem σ₀ hi)
      have h3 := card_fixFin_mul_of_disjoint hd
      rw [Perm.card_support_eq_two.2 hσ', Perm.card_support_eq_two.2 hτ] at h3
      rw [hpb]
      omega
  refine ⟨b, hb, isConj_iff.2 ⟨(w : G), by rw [hbdef, hb₀]; simp⟩, ?_, hcard⟩
  intro hbz
  have hzC : z ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hpb1 : permOf T.toBase θ hb = 1 :=
    (permOf_congr T.toBase θ hbz hb hzC).trans
      ((permOf_eq_one_iff T.toBase θ hzC).2 (T.cyc.le T.cyc.mem))
  have hfix1 : fixFin (1 : Perm (Fin n)) = Finset.univ := by
    ext i
    simp [mem_fixFin]
  rw [hpb1, hfix1, Finset.card_univ, Fintype.card_fin] at hcard
  omega

theorem exists_partner_of_wreathOutcome (T : Shape G L Q n z u)
    (θ : L ≃* alternatingGroup (Fin n)) (hn : 9 ≤ n) {x : G}
    (hx : x ∈ centralizer ({z} : Set G)) (hτ : (permOf T.toBase θ hx).IsSwap) (hx2 : x * x = 1)
    (hfus : ¬ IsConj z (z * x)) (hzx : z ∈ centralizer ({x} : Set G))
    (hW : WreathOutcome (QuotientGroup.mk (QuotientGroup.mk ⟨z, hzx⟩ : TwoSec x) : TwoSecO x)
      ((twoSecComp θ x (fixFin (permOf T.toBase θ hx))).map
        (QuotientGroup.mk' (CFSG.oddCore (TwoSec x)))) (n - 2)) :
    ∃ (b : G) (hb : b ∈ centralizer ({z} : Set G)), IsConj z b ∧ b ≠ z ∧
      ((fixFin (permOf T.toBase θ hb)).card = n - 4 ∨
        (fixFin (permOf T.toBase θ hb)).card = n - 6) := by
  classical
  have hz2 : z * z = 1 := T.cyc.mul_self
  set F : Finset (Fin n) := fixFin (permOf T.toBase θ hx) with hF
  have hFcard : F.card = n - 2 := card_fixFin_of_isSwap hτ
  obtain ⟨a₁, ha₁, a₂, ha₂, h12⟩ := Finset.one_lt_card.1 (show 1 < F.card by omega)
  have ha₂' : a₂ ∈ F.erase a₁ := Finset.mem_erase.2 ⟨h12.symm, ha₂⟩
  have h34 : 1 < ((F.erase a₁).erase a₂).card := by
    rw [Finset.card_erase_of_mem ha₂', Finset.card_erase_of_mem ha₁]
    omega
  obtain ⟨a₃, ha₃, a₄, ha₄, h34'⟩ := Finset.one_lt_card.1 h34
  simp only [Finset.mem_erase] at ha₃ ha₄
  obtain ⟨h32, h31, ha₃F⟩ := ha₃
  obtain ⟨h42, h41, ha₄F⟩ := ha₄
  set δ : Perm (Fin n) := swap a₁ a₂ * swap a₃ a₄ with hδ
  have hdisj12 : (swap a₁ a₂).Disjoint (swap a₃ a₄) := by
    intro i
    by_cases hi : i = a₁ ∨ i = a₂
    · right
      rcases hi with rfl | rfl
      · exact swap_apply_of_ne_of_ne h31.symm h41.symm
      · exact swap_apply_of_ne_of_ne h32.symm h42.symm
    · push Not at hi
      exact Or.inl (swap_apply_of_ne_of_ne hi.1 hi.2)
  have hδ2 : δ * δ = 1 := by
    rw [hδ]
    calc swap a₁ a₂ * swap a₃ a₄ * (swap a₁ a₂ * swap a₃ a₄) =
        swap a₁ a₂ * (swap a₃ a₄ * swap a₁ a₂) * swap a₃ a₄ := by group
      _ = swap a₁ a₂ * (swap a₁ a₂ * swap a₃ a₄) * swap a₃ a₄ := by
        rw [hdisj12.commute.eq]
      _ = 1 := by
        rw [← mul_assoc, swap_mul_self, one_mul, swap_mul_self]
  have hδF : δ ∈ altSub F := by
    refine mem_altSub.2 ⟨?_, fun i hi => ?_⟩
    · rw [hδ, Perm.sign_mul, Perm.sign_swap h12, Perm.sign_swap h34']; rfl
    · have hi1 : i ≠ a₁ := fun h' => hi (h' ▸ ha₁)
      have hi2 : i ≠ a₂ := fun h' => hi (h' ▸ ha₂)
      have hi3 : i ≠ a₃ := fun h' => hi (h' ▸ ha₃F)
      have hi4 : i ≠ a₄ := fun h' => hi (h' ▸ ha₄F)
      rw [hδ, Perm.mul_apply, swap_apply_of_ne_of_ne hi3 hi4, swap_apply_of_ne_of_ne hi1 hi2]
  have hδA : δ ∈ alternatingGroup (Fin n) := altSub_le_alternatingGroup F hδF
  set a' : L := θ.symm ⟨δ, hδA⟩ with ha'
  have hea' : ((θ a' : alternatingGroup (Fin n)) : Perm (Fin n)) = δ := by simp [ha']
  set a : G := (a' : G) with ha
  have haR : a ∈ corr (X := G) θ (altSub F) := mem_corr_of_mem (by rw [hea']; exact hδF)
  have hax : a ∈ centralizer ({x} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    exact (comm_of_mem_corr_of_permOf_fix T.toBase θ hx (fun i hi => mem_fixFin.1 hi) haR).symm
  have haL : a ∈ L := a'.2
  have haz : a ∈ centralizer ({z} : Set G) := le_cent_single T.std T.cyc haL
  have hpa : permOf T.toBase θ haz = δ := by
    rw [permOf_of_mem T.toBase θ haz haL]
    exact hea'
  have ha2 : a * a = 1 := by
    have : a' * a' = 1 := by
      apply θ.injective
      apply Subtype.ext
      rw [map_mul, map_one, Subgroup.coe_mul, hea', OneMemClass.coe_one]
      exact hδ2
    exact congrArg Subtype.val this
  have hzb2 : (QuotientGroup.mk ⟨z, hzx⟩ : TwoSec x) * QuotientGroup.mk ⟨z, hzx⟩ = 1 := by
    rw [← QuotientGroup.mk_mul]
    have : (⟨z, hzx⟩ : ↥(centralizer ({x} : Set G))) * ⟨z, hzx⟩ = 1 := Subtype.ext hz2
    rw [this]
    rfl
  have hab2 : (QuotientGroup.mk ⟨a, hax⟩ : TwoSec x) * QuotientGroup.mk ⟨a, hax⟩ = 1 := by
    rw [← QuotientGroup.mk_mul]
    have : (⟨a, hax⟩ : ↥(centralizer ({x} : Set G))) * ⟨a, hax⟩ = 1 := Subtype.ext ha2
    rw [this]
    rfl
  have haz' : a * z = z * a := mem_centralizer_singleton_iff.1 haz
  have hZA : (⟨z, hzx⟩ : ↥(centralizer ({x} : Set G))) * ⟨a, hax⟩ = ⟨a, hax⟩ * ⟨z, hzx⟩ :=
    Subtype.ext haz'.symm
  have hzab2 : (QuotientGroup.mk (⟨z, hzx⟩ * ⟨a, hax⟩ : ↥(centralizer ({x} : Set G))) :
      TwoSec x) * QuotientGroup.mk (⟨z, hzx⟩ * ⟨a, hax⟩ : ↥(centralizer ({x} : Set G))) = 1 := by
    rw [← QuotientGroup.mk_mul]
    have hZ : (⟨z, hzx⟩ : ↥(centralizer ({x} : Set G))) * ⟨z, hzx⟩ = 1 := Subtype.ext hz2
    have hA : (⟨a, hax⟩ : ↥(centralizer ({x} : Set G))) * ⟨a, hax⟩ = 1 := Subtype.ext ha2
    have : (⟨z, hzx⟩ * ⟨a, hax⟩ : ↥(centralizer ({x} : Set G))) * (⟨z, hzx⟩ * ⟨a, hax⟩) = 1 := by
      calc (⟨z, hzx⟩ * ⟨a, hax⟩ : ↥(centralizer ({x} : Set G))) * (⟨z, hzx⟩ * ⟨a, hax⟩) =
          ⟨z, hzx⟩ * (⟨a, hax⟩ * ⟨z, hzx⟩) * ⟨a, hax⟩ := by group
        _ = ⟨z, hzx⟩ * (⟨z, hzx⟩ * ⟨a, hax⟩) * ⟨a, hax⟩ := by rw [hZA]
        _ = (⟨z, hzx⟩ * ⟨z, hzx⟩) * (⟨a, hax⟩ * ⟨a, hax⟩) := by group
        _ = 1 := by rw [hZ, hA, one_mul]
    rw [this]
    rfl
  have habB : (QuotientGroup.mk (QuotientGroup.mk ⟨a, hax⟩ : TwoSec x) : TwoSecO x) ∈
      (twoSecComp θ x F).map (QuotientGroup.mk' (CFSG.oddCore (TwoSec x))) :=
    Subgroup.mem_map_of_mem _ ⟨⟨a, hax⟩, Subgroup.mem_subgroupOf.2 haR, rfl⟩
  have hzbb2 : (QuotientGroup.mk (QuotientGroup.mk ⟨z, hzx⟩ : TwoSec x) : TwoSecO x) *
      QuotientGroup.mk (QuotientGroup.mk ⟨z, hzx⟩ : TwoSec x) = 1 := by
    rw [← QuotientGroup.mk_mul, hzb2]
    rfl
  have habb2 : (QuotientGroup.mk (QuotientGroup.mk ⟨a, hax⟩ : TwoSec x) : TwoSecO x) *
      QuotientGroup.mk (QuotientGroup.mk ⟨a, hax⟩ : TwoSec x) = 1 := by
    rw [← QuotientGroup.mk_mul, hab2]
    rfl
  obtain ⟨k, hk⟩ := exists_conj_mul_of_wreath (by omega) hzbb2 habb2 hW habB
  obtain ⟨wb, hwb⟩ := exists_conj_of_mk_conj_oddCore hzb2 hzab2 (k := k)
    (by rw [hk, QuotientGroup.mk_mul, QuotientGroup.mk_mul])
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective wb
  set b₀ : ↥(centralizer ({x} : Set G)) := w * ⟨z, hzx⟩ * w⁻¹ with hb₀
  have hmkb : (QuotientGroup.mk b₀ : TwoSec x) =
      QuotientGroup.mk (⟨z, hzx⟩ * ⟨a, hax⟩ : ↥(centralizer ({x} : Set G))) := by
    rw [hb₀, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact hwb
  set b : G := (b₀ : G) with hbdef
  have hbx : b ∈ centralizer ({x} : Set G) := b₀.2
  have hmkb' : (QuotientGroup.mk ⟨b, hbx⟩ : TwoSec x) =
      QuotientGroup.mk (⟨z, hzx⟩ * ⟨a, hax⟩ : ↥(centralizer ({x} : Set G))) := hmkb
  have hb : b ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    refine comm_of_mk_comm hx2 hfus hzx hbx ?_
    rw [hmkb', ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    calc (⟨z, hzx⟩ * ⟨a, hax⟩ : ↥(centralizer ({x} : Set G))) * ⟨z, hzx⟩ =
        ⟨z, hzx⟩ * (⟨a, hax⟩ * ⟨z, hzx⟩) := by group
      _ = ⟨z, hzx⟩ * (⟨z, hzx⟩ * ⟨a, hax⟩) := by rw [hZA]
  have hbza : b = z * a ∨ b = z * a * x := by
    have h2 := (mem_zpowers_selfC_iff hx2).1 (QuotientGroup.eq.1 hmkb'.symm)
    rcases h2 with h2 | h2
    · left
      have h2' : (z * a)⁻¹ * b = 1 := by simpa using h2
      exact (inv_mul_eq_one.1 h2').symm
    · right
      have h2' : (z * a)⁻¹ * b = x := by simpa using h2
      calc b = (z * a) * ((z * a)⁻¹ * b) := by group
        _ = z * a * x := by rw [h2']
  have hzC : z ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hpz : permOf T.toBase θ hzC = 1 :=
    (permOf_eq_one_iff T.toBase θ hzC).2 (T.cyc.le T.cyc.mem)
  have hza : z * a ∈ centralizer ({z} : Set G) := mul_mem hzC haz
  have hpza : permOf T.toBase θ hza = δ := by
    rw [permOf_mul T.toBase θ hzC haz hza, hpz, one_mul, hpa]
  have hdτ : δ.Disjoint (permOf T.toBase θ hx) := by
    intro i
    by_cases hi : i ∈ F
    · exact Or.inr (mem_fixFin.1 hi)
    · exact Or.inl ((mem_altSub.1 hδF).2 i hi)
  have hsuppδ : δ.support.card = 4 := by
    rw [hδ, hdisj12.card_support_mul, card_support_swap h12, card_support_swap h34']
  have hcard : (fixFin (permOf T.toBase θ hb)).card = n - 4 ∨
      (fixFin (permOf T.toBase θ hb)).card = n - 6 := by
    rcases hbza with h1 | h1
    · left
      have hpb : permOf T.toBase θ hb = δ := (permOf_congr T.toBase θ h1 hb hza).trans hpza
      have h3 := card_fixFin_add_card_support (permOf T.toBase θ hb)
      rw [hpb, hsuppδ] at h3
      rw [hpb]
      omega
    · right
      have hzax : z * a * x ∈ centralizer ({z} : Set G) := mul_mem hza hx
      have hpb : permOf T.toBase θ hb = δ * permOf T.toBase θ hx :=
        (permOf_congr T.toBase θ h1 hb hzax).trans
          (by rw [permOf_mul T.toBase θ hza hx hzax, hpza])
      have h3 := card_fixFin_mul_of_disjoint hdτ
      rw [hsuppδ, Perm.card_support_eq_two.2 hτ] at h3
      rw [hpb]
      omega
  refine ⟨b, hb, isConj_iff.2 ⟨(w : G), by rw [hbdef, hb₀]; simp⟩, ?_, hcard⟩
  intro hbz
  have hpb1 : permOf T.toBase θ hb = 1 := (permOf_congr T.toBase θ hbz hb hzC).trans hpz
  have hfix1 : fixFin (1 : Perm (Fin n)) = Finset.univ := by
    ext i
    simp [mem_fixFin]
  rw [hpb1, hfix1, Finset.card_univ, Fintype.card_fin] at hcard
  omega

end Outcomes

section Cases

theorem twoSec_cases_of_exactShape (htri : ExactShapeTrichotomy) (T : Shape G L Q n z u)
    (θ : L ≃* alternatingGroup (Fin n)) (hn : 11 ≤ n) {x : G}
    (hx : x ∈ centralizer ({z} : Set G)) (hτ : (permOf T.toBase θ hx).IsSwap) (hx2 : x * x = 1)
    (hfus : ¬ IsConj z (z * x)) (hzx : z ∈ centralizer ({x} : Set G))
    (hE : ExactShape (QuotientGroup.mk (QuotientGroup.mk ⟨z, hzx⟩ : TwoSec x) : TwoSecO x)
      ((twoSecComp θ x (fixFin (permOf T.toBase θ hx))).map
        (QuotientGroup.mk' (CFSG.oddCore (TwoSec x)))) (n - 2)) :
    (∀ c ∈ centralizer ({x} : Set G), ∃ o ∈ oddCoreOf (centralizer ({x} : Set G)),
        o * c ∈ centralizer ({z} : Set G)) ∨
      (∃ (b : G) (hb : b ∈ centralizer ({z} : Set G)), IsConj z b ∧ b ≠ z ∧
        ((fixFin (permOf T.toBase θ hb)).card = n - 2 ∨
          (fixFin (permOf T.toBase θ hb)).card = n - 4 ∨
          (fixFin (permOf T.toBase θ hb)).card = n - 6)) ∨ n = 12 := by
  have hx1 := (swap_elt_ne T.toBase θ hx hτ).2
  rcases htri (TwoSecO x) _ _ (n - 2) (by omega) (isKGroupCat_twoSecO T.std hx1)
      (oddCore_twoSecO_eq_bot x) hE with h1 | h1 | h1 | h1
  · exact Or.inl fun c hc =>
      exists_oddCoreOf_mul_mem_centralizer hx2 T.cyc.mul_self hfus hzx h1 hc
  · obtain ⟨b, hb, h2, h3, h4⟩ :=
      exists_partner_of_wreathOutcome T θ (by omega) hx hτ hx2 hfus hzx h1
    exact Or.inr (Or.inl ⟨b, hb, h2, h3, Or.inr h4⟩)
  · obtain ⟨b, hb, h2, h3, h4⟩ :=
      exists_partner_of_symOutcome T θ (by omega) hx hτ hx2 hfus hzx h1
    exact Or.inr (Or.inl ⟨b, hb, h2, h3, h4.elim Or.inl (fun h5 => Or.inr (Or.inl h5))⟩)
  · exact Or.inr (Or.inr (by omega))

theorem twoSec_cases_O (htri : ExactShapeTrichotomy) (hlookup : AltComponentLookup)
    (hHN : CFSG.ComponentClassification.RestrictedStd.Spor.HNLocalComponentsInput)
    (hOut : CFSG.RankThree.PartOne.SporadicOuterOrderLeTwoSimple)
    (hFour : CFSG.ComponentClassification.RestrictedStd.Spor.FourExactOuterInput)
    (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n)) (hn : 11 ≤ n) {x : G}
    (hx : x ∈ centralizer ({z} : Set G)) (hτ : (permOf T.toBase θ hx).IsSwap) (hx2 : x * x = 1)
    (hfus : ¬ IsConj z (z * x)) (hzx : z ∈ centralizer ({x} : Set G)) :
    (∀ c ∈ centralizer ({x} : Set G), ∃ o ∈ oddCoreOf (centralizer ({x} : Set G)),
        o * c ∈ centralizer ({z} : Set G)) ∨
      (∃ (b : G) (hb : b ∈ centralizer ({z} : Set G)), IsConj z b ∧ b ≠ z ∧
        ((fixFin (permOf T.toBase θ hb)).card = n - 2 ∨
          (fixFin (permOf T.toBase θ hb)).card = n - 4 ∨
          (fixFin (permOf T.toBase θ hb)).card = n - 6)) ∨ n = 12 :=
  twoSec_cases_of_exactShape htri T θ hn hx hτ hx2 hfus hzx
    (exactShape_twoSecO hlookup hHN hOut hFour T.std θ hn T.cyc T.card hx
      (cent_le_normalizer T.std T.cyc hx) hτ hx2 hfus hzx)

end Cases

end CFSG.OddStandard.AltStdCycTwo.Two
