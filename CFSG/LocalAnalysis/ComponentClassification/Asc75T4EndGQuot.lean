module

public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4EndGTransfer

public section

namespace CFSG.ComponentClassification.Asc75T4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem5
open CFSG.ComponentClassification.AschbacherTheorem5.SectionSix
open CFSG.GorensteinWalter

section TwoPower

variable {X : Type*} [Group X]

theorem mem_of_pow_two_pow_eq_one {N : Subgroup X} [N.Normal] (hN : Odd N.index) {x : X}
    {k : ℕ} (hx : x ^ 2 ^ k = 1) : x ∈ N := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hx)
  have hcop : N.index.Coprime (orderOf x) := by
    rw [hj]
    exact Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hN)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact pow_mem (N.pow_index_mem x) m

theorem le_of_isPGroup {N P : Subgroup X} [N.Normal] (hN : Odd N.index) (hP : IsPGroup 2 P) :
    P ≤ N := by
  intro x hx
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  exact mem_of_pow_two_pow_eq_one hN (k := k) (by simpa using congrArg Subtype.val hk)

theorem eq_one_of_pow_two_pow_eq_one {C : Subgroup X} (hC : Odd (Nat.card C)) {x : X}
    (hxC : x ∈ C) {k : ℕ} (hx : x ^ 2 ^ k = 1) : x = 1 := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hx)
  have h1 : orderOf x ∣ Nat.card C := by
    have := orderOf_dvd_natCard (⟨x, hxC⟩ : C)
    rwa [Subgroup.orderOf_mk] at this
  rcases j with _ | j
  · rwa [pow_zero, orderOf_eq_one_iff] at hj
  · rw [hj] at h1
    exact absurd (hC.of_dvd_nat ((dvd_pow_self 2 (Nat.succ_ne_zero j)).trans h1))
      (Nat.not_odd_iff_even.mpr even_two)

end TwoPower

variable {G : Type} [Group G] [Finite G]

theorem odd_card_pPrimeCore : Odd (Nat.card (pPrimeCore 2 G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Nat.coprime_two_left.mp pPrimeCore_coprime_card

namespace EndSetting

variable {Q : Subgroup G} (hE : EndSetting Q)
include hE

theorem nonempty_endSylow : Nonempty (EndSylow Q) := by
  obtain ⟨t, ht⟩ := hE.exists_isOverlapInv
  obtain ⟨S, hS, htS⟩ := exists_isSylowOf_le
    (isPGroup_zpowers_of_pow_eq_one (k := 1) (by simpa using ht.1))
    ((zpowers_le).mpr ht.mem_normalizer)
  exact ⟨⟨t, ht, S, hS, htS (mem_zpowers t)⟩⟩

theorem pPrimeCore_le_normalizer : pPrimeCore 2 G ≤ normalizer (Q : Set G) := by
  obtain ⟨E, hEK, hE2, hE4⟩ := hE.main.four
  refine le_normalizer_of_fourGroup hE.main.tight (hEK.trans (twoPrimeLayerIn_le Q)) hE2 hE4
    odd_card_pPrimeCore ?_
  rw [normalizer_eq_top_iff.mpr inferInstance]
  exact le_top

theorem toBar_mem_centralizer_of_mem {o : normalizer (Q : Set G)}
    (ho : (o : G) ∈ pPrimeCore 2 G) :
    toBar Q o ∈ centralizer (bar Q (twoPrimeLayerIn Q) : Set (Bar Q)) := by
  set L := bar Q (twoPrimeLayerIn Q) with hL
  set B := bar Q (pPrimeCore 2 G) with hB
  have hLs : IsSimpleGroup L := hE.isSimpleGroup_bar
  have hBn : B.Normal := by
    have : ((pPrimeCore 2 G).subgroupOf (normalizer (Q : Set G))).Normal :=
      Subgroup.normal_subgroupOf
    exact this.map _ (toBar_surjective Q)
  have hBodd : Odd (Nat.card B) := odd_card_pPrimeCore.of_dvd_nat (card_bar_dvd _)
  have hBL : B ⊓ L = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (B.subgroupOf L) with h | h
    · exact disjoint_iff.mp (subgroupOf_eq_bot.mp h)
    · exfalso
      have hLB : L ≤ B := subgroupOf_eq_top.mp h
      have h1 : Odd (Nat.card L) := hBodd.of_dvd_nat (Subgroup.card_dvd_of_le hLB)
      exact Nat.not_even_iff_odd.mpr h1 hE.main.hasFourGroup_bar.even_card
  have hoB : toBar Q o ∈ B := toBar_mem_bar Q ho
  rw [mem_centralizer_iff]
  intro l hl
  have hc : toBar Q o * l * (toBar Q o)⁻¹ * l⁻¹ ∈ B ⊓ L := by
    refine mem_inf.mpr ⟨?_, ?_⟩
    · have h1 : l * (toBar Q o)⁻¹ * l⁻¹ ∈ B := hBn.conj_mem _ (inv_mem hoB) l
      have h2 := mul_mem hoB h1
      rwa [show toBar Q o * (l * (toBar Q o)⁻¹ * l⁻¹) = toBar Q o * l * (toBar Q o)⁻¹ * l⁻¹ by
        group] at h2
    · have h1 : toBar Q o * l * (toBar Q o)⁻¹ ∈ L :=
        (bar_twoPrimeLayerIn_normal Q).conj_mem l hl _
      exact mul_mem h1 (inv_mem hl)
  rw [hBL, mem_bot] at hc
  calc l * toBar Q o = (toBar Q o * l * (toBar Q o)⁻¹ * l⁻¹)⁻¹ * (toBar Q o * l) := by group
    _ = toBar Q o * l := by rw [hc, inv_one, one_mul]

theorem map_normalizer_ne_top :
    (normalizer (Q : Set G)).map (QuotientGroup.mk' (pPrimeCore 2 G)) ≠ ⊤ := by
  intro h
  apply hE.main.proper
  have h1 := Subgroup.comap_map_eq_self (f := QuotientGroup.mk' (pPrimeCore 2 G))
    (H := normalizer (Q : Set G)) (by rw [QuotientGroup.ker_mk']; exact hE.pPrimeCore_le_normalizer)
  rw [← h1, h, comap_top]

theorem false_of_normal_le_map {N : Subgroup (G ⧸ pPrimeCore 2 G)} [N.Normal]
    (hN : Odd N.index) (hNH : N ≤ (normalizer (Q : Set G)).map (QuotientGroup.mk' _)) :
    False := by
  set π := QuotientGroup.mk' (pPrimeCore 2 G) with hπ
  have hOH := hE.pPrimeCore_le_normalizer
  have hNH' : N.comap π ≤ normalizer (Q : Set G) := by
    intro x hx
    obtain ⟨h, hh, hhx⟩ := hNH hx
    have h1 : h⁻¹ * x ∈ pPrimeCore 2 G := QuotientGroup.eq.mp hhx
    have h2 := mul_mem hh (hOH h1)
    rwa [mul_inv_cancel_left] at h2
  obtain ⟨E, hEK, hE2, hE4⟩ := hE.main.four
  have hidx : Odd (N.comap π).index := by
    rwa [index_comap_of_surjective N (QuotientGroup.mk'_surjective _)]
  have hEN : E ≤ N.comap π := le_of_isPGroup hidx (isPGroup_of_sq_eq_one hE2)
  obtain ⟨g, hg⟩ : ∃ g : G, g ∉ normalizer (Q : Set G) := by
    by_contra h
    push Not at h
    exact hE.main.proper (eq_top_iff.mpr fun x _ => h x)
  apply hE.main.not_hasFourGroup_of_linkedClass_eq hE.linked hg
  refine ((hasFourGroup_rightConjugate_iff (g := g)).mpr ⟨E, le_rfl, hE2, hE4⟩).mono ?_
  intro y hy
  have h1 : g * y * g⁻¹ ∈ E := (mem_rightConjugate_iff E g y).mp hy
  refine mem_inf.mpr ⟨(mem_rightConjugate_iff Q g y).mpr
    ((hEK.trans (twoPrimeLayerIn_le Q)) h1), hNH' ?_⟩
  have h2 := (inferInstance : (N.comap π).Normal).conj_mem _ (hEN h1) g⁻¹
  rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at h2

end EndSetting

namespace PSLModel

variable {Q : Subgroup G} (M : PSLModel Q) (hE : EndSetting Q)
include hE

theorem psi_toBar_eq_one {o : normalizer (Q : Set G)} (ho : (o : G) ∈ pPrimeCore 2 G) :
    M.psi (toBar Q o) = 1 :=
  (M.psi_eq_one_iff _).mpr (hE.toBar_mem_centralizer_of_mem ho)

end PSLModel

namespace PSLModel

variable {Q : Subgroup G} (M : PSLModel Q) (hE : EndSetting Q)
include hE

theorem card_pgl_dvd {N : Subgroup (G ⧸ pPrimeCore 2 G)} [N.Normal] (hN : Odd N.index) :
    Nat.card (pGammaL2PGLRange M.F) ∣
      Nat.card ((N.comap (QuotientGroup.mk' (pPrimeCore 2 G)) ⊓
        normalizer (Q : Set G)).map (QuotientGroup.mk' (pPrimeCore 2 G))) := by
  set π := QuotientGroup.mk' (pPrimeCore 2 G) with hπ
  set Y := N.comap π ⊓ normalizer (Q : Set G) with hY
  have hYH : Y ≤ normalizer (Q : Set G) := inf_le_right
  let Φ : Y →* PGammaL2 M.F := M.psi.comp ((toBar Q).comp (inclusion hYH))
  let ρ : Y →* G ⧸ pPrimeCore 2 G := π.comp Y.subtype
  have hρ : ρ.range = Y.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : ρ.ker ≤ Φ.ker := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy ⊢
    have hyO : (y : G) ∈ pPrimeCore 2 G := (QuotientGroup.eq_one_iff _).mp hy
    exact M.psi_toBar_eq_one hE (o := inclusion hYH y) hyO
  have hdvd : Nat.card Φ.range ∣ Nat.card ρ.range := by
    rw [← Subgroup.index_ker, ← Subgroup.index_ker]
    exact Subgroup.index_dvd_of_le hker
  rw [← hρ]
  refine (Subgroup.card_dvd_of_le ?_).trans hdvd
  have hpow : ∀ h : normalizer (Q : Set G), (h : G) ^ N.index ∈ Y := fun h =>
    mem_inf.mpr ⟨by rw [mem_comap, map_pow]; exact N.pow_index_mem _, pow_mem h.2 _⟩
  set L := bar Q (twoPrimeLayerIn Q) with hL
  set B := bar Q Y with hB
  have hLs : IsSimpleGroup L := hE.isSimpleGroup_bar
  have hBn : B.Normal := by
    have : (Y.subgroupOf (normalizer (Q : Set G))).Normal := by
      rw [hY, inf_subgroupOf_right]
      exact Subgroup.normal_subgroupOf
    exact this.map _ (toBar_surjective Q)
  have hLB : L ≤ B := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (B.subgroupOf L) with h | h
    · exfalso
      have hBL : B ⊓ L = ⊥ := disjoint_iff.mp (subgroupOf_eq_bot.mp h)
      obtain ⟨E, hEL, hE2, hE4⟩ := hE.main.hasFourGroup_bar
      obtain ⟨l, hlE, hl1⟩ : ∃ l ∈ E, l ≠ 1 := by
        by_contra hcon
        push Not at hcon
        have : E = ⊥ := eq_bot_iff.mpr fun x hx => mem_bot.mpr (hcon x hx)
        rw [this, card_bot] at hE4
        omega
      obtain ⟨h, rfl⟩ := toBar_surjective Q l
      have h1 : toBar Q h ^ N.index ∈ B ⊓ L := by
        refine mem_inf.mpr ⟨?_, pow_mem (hEL hlE) _⟩
        rw [← map_pow]
        exact toBar_mem_bar Q (by simpa using hpow h)
      rw [hBL, mem_bot] at h1
      obtain ⟨j, hj⟩ := hN
      rw [hj, pow_succ, pow_mul, hE2 _ hlE, one_pow, one_mul] at h1
      exact hl1 h1
    · exact subgroupOf_eq_top.mp h
  have hpsl : pGammaL2PSLRange M.F ≤ Φ.range := by
    rintro _ ⟨w, rfl⟩
    have hn : ((M.e.symm w : L) : Bar Q) ∈ B := hLB (M.e.symm w).2
    obtain ⟨h, hhY, hh⟩ := (mem_bar_iff Q Y _).mp hn
    refine ⟨⟨h, hhY⟩, ?_⟩
    change M.psi (toBar Q h) = _
    rw [hh, M.psi_apply_of_mem, MulEquiv.apply_symm_apply]
    rfl
  obtain ⟨t, ht⟩ := hE.exists_isOverlapInv
  have htY : t ∈ Y := mem_inf.mpr ⟨mem_comap.mpr (mem_of_pow_two_pow_eq_one hN (k := 1)
    (by simpa using congrArg π ht.1)), ht.mem_normalizer⟩
  obtain ⟨hpgl, hpsl'⟩ := M.outerDiagonal hE ht
  have hΦt : Φ ⟨t, htY⟩ = M.psi (toBar Q ⟨t, ht.mem_normalizer⟩) := rfl
  intro x hx
  by_cases hxs : x ∈ pGammaL2PSLRange M.F
  · exact hpsl hxs
  · have h1 := hpsl (M.mul_mem_psl hx hpgl hxs hpsl')
    rw [← hΦt] at h1
    have h2 := mul_mem h1 (inv_mem (MonoidHom.mem_range.mpr ⟨⟨t, htY⟩, rfl⟩))
    rwa [mul_inv_cancel_right] at h2

end PSLModel

namespace MainCounterexample

variable {Q : Subgroup G} (hM : MainCounterexample G Q) (hE : EndSetting Q)
include hM hE

theorem exists_mulEquiv_dihedral
    (X : EndSylow Q) (M : PSLModel Q) :
    ∃ m : ℕ, 1 ≤ m ∧ Nonempty (X.S ≃* DihedralGroup (2 ^ m)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd := hM.odd_card_centralizer hE
  have hSP := hM.S_le_P hE X M
  let f₀ : X.S →* PGammaL2 M.F := M.psi.comp ((toBar Q).comp (inclusion X.S_le))
  have hf₀ : ∀ s : X.S, f₀ s ∈ pGammaL2PGLRange M.F := fun s =>
    (X.mem_P_iff_psi_mem hE M hodd s.2).mp (hSP s.2)
  let f : X.S →* PGL2 M.F :=
    (pGammaL2PGLRangeEquiv M.F).symm.toMonoidHom.comp (f₀.codRestrict _ hf₀)
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro s hs
    have h1 : f₀ s = 1 := by
      have h := congrArg (fun x => ((pGammaL2PGLRangeEquiv M.F x : pGammaL2PGLRange M.F) :
        PGammaL2 M.F)) hs
      simpa [f] using h
    have h2 := (M.psi_eq_one_iff _).mp h1
    obtain ⟨k, hk⟩ := X.hS.isPGroup s
    have h3 : toBar Q (inclusion X.S_le s) = 1 := by
      refine eq_one_of_pow_two_pow_eq_one hodd h2 (k := k) ?_
      rw [← map_pow, ← map_pow, hk, map_one, map_one]
    have h4 := toBar_injOn_of_isPGroup X.hS.isPGroup s.2 (one_mem X.S)
      (h3.trans (map_one _).symm)
    have h5 : (s : G) = 1 := congrArg Subtype.val h4
    exact Subtype.ext h5
  let eW : X.S ≃* f.range := MonoidHom.ofInjective hinj
  have hW : IsPGroup 2 f.range := X.hS.isPGroup.of_equiv eW
  have : Finite (PGL2 M.F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow 2 (PGL2 M.F)))
  have hT : IsSylowOf 2 (T : Subgroup (PGL2 M.F)) ⊤ :=
    isSylowOf_iff.mpr ⟨le_top, T.isPGroup', by rw [relIndex_top_right]; exact T.not_dvd_index⟩
  have hTd : AschbacherTheorem3.IsDihedralTwoGroup (T : Subgroup (PGL2 M.F)) := by
    obtain ⟨m, hm, ⟨eT⟩⟩ := pgl2_odd_hasDihedralSylowTwo_model M.F M.hF T
    exact ⟨m + 1, by omega, by rw [Nat.add_sub_cancel]; exact ⟨eT⟩⟩
  rcases isCyclic_or_dihedral_of_isSylowOf hT hTd le_top hW with hcyc | ⟨k, hk, ⟨e'⟩⟩
  · exfalso
    have : IsCyclic X.S := (MulEquiv.isCyclic eW).mpr hcyc
    exact not_hasFourGroup_of_isCyclic_or_quaternion (Or.inl this)
      ((hE.hasFourGroup_inf X.hS).mono inf_le_left)
  · exact ⟨k, hk, ⟨eW.trans e'⟩⟩

theorem hasDihedralSylowTwo :
    CFSG.GorensteinWalter.HasDihedralSylowTwo G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨X⟩ := hE.nonempty_endSylow
  obtain ⟨M⟩ := hE.nonempty_pslModel
  obtain ⟨m, hm, ⟨e⟩⟩ := hM.exists_mulEquiv_dihedral hE X M
  have hidx : ¬ 2 ∣ X.S.index := by
    have := (isSylowOf_iff.mp (hE.isSylowOf_top X.hS)).2.2
    rwa [relIndex_top_right] at this
  intro T
  exact ⟨m, hm, ⟨(Sylow.equiv T (X.hS.isPGroup.toSylow hidx)).trans
    ((MulEquiv.subgroupCongr (IsPGroup.toSylow_coe _ _)).trans e)⟩⟩

end MainCounterexample

end CFSG.ComponentClassification.Asc75T4
