module

public import CFSG.LocalAnalysis.ABGTheoremB.PropR2Input
public import CFSG.GroupTheory.ABGDGroups.LinearEmbedding
import CFSG.GroupTheory.ABGDGroups.LinearQuotient
import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderThreeComplement
import CFSG.LocalAnalysis.ABGTheoremB.IV1
public import CFSG.LocalAnalysis.ABGTheoremB.Facts
import CFSG.GroupTheory.QuasiDihedralFusion.SemidihedralModel

public section

namespace CFSG.ABGTheoremB

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools
open CFSG.GorensteinWalter (PGammaL2 PSL2 pGammaL2PSLRange)

section Wreath

open CFSG.Open CFSG.Semidihedral
open CFSG.Wreathed (Wreath)

private theorem cr23_wreath_half_involution (k : ℕ) :
    orderOf (Wreathed.element (2 ^ (k + 1)) ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) 0 0) = 2 ∧
      Wreathed.element (2 ^ (k + 1)) 0 0 1 *
          Wreathed.element (2 ^ (k + 1)) ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) 0 0 *
          (Wreathed.element (2 ^ (k + 1)) 0 0 1)⁻¹ ≠
        Wreathed.element (2 ^ (k + 1)) ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) 0 0 := by
  refine ⟨(Wreathed.element_base_involution_iff k _ _).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩)), ?_⟩
  rw [Wreathed.conjugate_base_by_swap]
  intro h
  rw [Wreathed.element_eq_iff] at h
  exact Wreathed.half_residue_ne_zero k h.1.symm

private theorem cr23_wreath_not_embed {n k : ℕ} (hn : 4 ≤ n) (hk : 1 ≤ k)
    (ι : Wreath (2 ^ (k + 1)) →* SemidihedralGroup n) (hι : Function.Injective ι) : False := by
  have := presentation_finite n (by omega)
  obtain ⟨hx2, hxw⟩ := cr23_wreath_half_involution k
  set x := Wreathed.element (2 ^ (k + 1)) ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) 0 0 with hx
  set y := Wreathed.element (2 ^ (k + 1)) 1 0 0 with hy
  set w := Wreathed.element (2 ^ (k + 1)) 0 0 1 with hw
  have hxy : x * y = y * x := by
    rw [hx, hy, Wreathed.element_base_mul, Wreathed.element_base_mul, Wreathed.element_eq_iff]
    exact ⟨add_comm _ _, rfl, rfl⟩
  have hy2 : y ^ 2 ≠ 1 := by
    rw [hy, Wreathed.element_base_pow]
    intro h2
    rw [Wreathed.element_base_eq_one_iff] at h2
    have h2' : ((2 : ℕ) : ZMod (2 ^ (k + 1))) = 0 := by simpa [nsmul_eq_mul] using h2.1
    rw [ZMod.natCast_eq_zero_iff] at h2'
    have hle := Nat.le_of_dvd (by norm_num) h2'
    have h4 : 2 ^ 2 ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hX2 : orderOf (ι x) = 2 := by rw [orderOf_injective ι hι, hx2]
  have hXz : ι x ∉ Subgroup.zpowers (z n) := by
    intro h
    rcases (KleinFourOddKernel.mem_zpowers_involution _ _ (orderOf_z n (by omega))).mp h with
      h1 | h1
    · rw [h1, orderOf_one] at hX2
      omega
    · apply hxw
      apply hι
      rw [map_mul, map_mul, map_inv, h1,
        Subgroup.mem_center_iff.mp (z_mem_center n hn) (ι w), mul_inv_cancel_right]
  obtain ⟨h1, -, -⟩ := Local.semidihedral_four_subgroup_centralizers n hn
    (MulEquiv.refl (SemidihedralGroup n))
  have hz : (MulEquiv.refl (SemidihedralGroup n)) (r n) ^ (2 ^ (n - 1) / 2) = z n := by
    rw [MulEquiv.refl_apply, two_pow_div_two hn]
    rfl
  rw [hz] at h1
  obtain ⟨hC, hK⟩ := h1 (ι x) hX2 hXz
  have hYC : ι y ∈ Subgroup.centralizer ({ι x} : Set (SemidihedralGroup n)) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hxy]
  rw [hC] at hYC
  have hYsq := congrArg Subtype.val (IsKleinFour.mul_self (⟨ι y, hYC⟩ :
    Subgroup.closure ({z n, ι x} : Set (SemidihedralGroup n))))
  apply hy2
  apply hι
  rw [map_pow, map_one, pow_two]
  exact hYsq

private theorem cr23_not_hasWreathedSylow {G : Type} [Group G] [Finite G] {n : ℕ}
    (hG : HasSemidihedralSylow G n) (K : Subgroup G) (m : ℕ) : ¬ HasWreathedSylow K m := by
  rintro ⟨hm, hW⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 K) := inferInstance
  obtain ⟨e⟩ := hW P
  have hP' : IsPGroup 2 ((P : Subgroup K).map K.subtype) := P.isPGroup'.map K.subtype
  obtain ⟨S', hS'⟩ := hP'.exists_le_sylow
  obtain ⟨f'⟩ := hG.2 S'
  let ι : Wreath (2 ^ m) →* SemidihedralGroup n :=
    f'.symm.toMonoidHom.comp ((Subgroup.inclusion hS').comp
      (((P : Subgroup K).equivMapOfInjective K.subtype K.subtype_injective).toMonoidHom.comp
        e.symm.toMonoidHom))
  have hι : Function.Injective ι := by
    intro a b hab
    have h1 := congrArg Subtype.val (f'.symm.injective hab)
    apply e.symm.injective
    exact Subtype.ext (Subtype.ext h1)
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  exact cr23_wreath_not_embed hG.1 (by omega) ι hι

end Wreath

section Linear

variable {H : Type} [Group H] [Finite H]

private theorem cr23_mem_normalizer_of_conj_mem {J : Subgroup H} {g : H}
    (h : ∀ y ∈ J, g * y * g⁻¹ ∈ J) : g ∈ Subgroup.normalizer (J : Set H) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

private theorem cr23_normalizer_le_normalizer_map {Y : Subgroup H} (A : Subgroup Y)
    [hA : A.Characteristic] :
    Subgroup.normalizer (Y : Set H) ≤
      Subgroup.normalizer ((A.map Y.subtype : Subgroup H) : Set H) := by
  intro g hg
  apply cr23_mem_normalizer_of_conj_mem
  rintro _ ⟨a, ha, rfl⟩
  have hfix := hA.fixed (Subgroup.normalizerMonoidHom Y ⟨g, hg⟩)
  have hmem : a ∈ Subgroup.comap (Subgroup.normalizerMonoidHom Y ⟨g, hg⟩).toMonoidHom A := by
    rw [hfix]
    exact ha
  refine ⟨_, hmem, ?_⟩
  change (((Subgroup.normalizerMonoidHom Y ⟨g, hg⟩) a : Y) : H) = g * a * g⁻¹
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe]

omit [Finite H] in
private theorem cr23_normal_of_commutator_le {K : Subgroup H} (hK : commutator H ≤ K) :
    K.Normal := by
  refine ⟨fun k hk g => ?_⟩
  have hc : g * k * g⁻¹ * k⁻¹ ∈ K := hK (Subgroup.commutator_mem_commutator
    (Subgroup.mem_top g) (Subgroup.mem_top k))
  have h := K.mul_mem hc hk
  rwa [inv_mul_cancel_right] at h

private theorem cr23_mem_normalizer_of_mem_centralizer {J : Subgroup H} {g : H}
    (hg : g ∈ Subgroup.centralizer (J : Set H)) : g ∈ Subgroup.normalizer (J : Set H) := by
  apply cr23_mem_normalizer_of_conj_mem
  intro y hy
  rw [← (Subgroup.mem_centralizer_iff.mp hg) y hy, mul_inv_cancel_right]
  exact hy

theorem sup_normalizer_eq_top_of_linearDecomposition {F : Type} [Field F] [Finite F]
    {ι : H →* PGammaL2 F} {L E : Subgroup H} {S : Sylow 2 H}
    (hd : CFSG.ABGDGroups.IsLinearDecomposition ι L E S) (h3 : 3 < Nat.card F) (D : Subgroup H)
    {x : H} (hx : x ∈ (S : Subgroup H))
    (hxS : (S : Subgroup H) ≤ Subgroup.centralizer ({x} : Set H)) (p : ℕ) {PE : Subgroup H}
    (hPE : PE ≤ E) (N : Subgroup H) [hN : N.Normal] (hN1 : N ≠ ⊥) :
    N ⊔ Subgroup.normalizer ((pCoreIn p ((CFSG.ABGDGroups.linearCore ι ⊔ D) ⊓
      Subgroup.centralizer ({x} : Set H)) ⊔ PE : Subgroup H) : Set H) = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L₀ := CFSG.ABGDGroups.linearCore ι with hL₀
  set K₀ : Subgroup H := (L₀ ⊔ D) ⊓ Subgroup.centralizer ({x} : Set H) with hK₀
  set Ubar : Subgroup H := pCoreIn p K₀ ⊔ PE with hUbar
  have hL₀n : L₀.Normal := hd.linearCore_normal
  have hL₀N : L₀ ≤ N := by
    obtain ⟨e⟩ := hd.nonempty_linearCore_mulEquiv
    have : IsSimpleGroup (PSL2 F) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
    have hsimple : IsSimpleGroup L₀ := e.isSimpleGroup
    have hNL : (N.subgroupOf L₀).Normal := hN.subgroupOf L₀
    rcases hsimple.eq_bot_or_eq_top_of_normal (N.subgroupOf L₀) with hbot | htop
    · exfalso
      apply hN1
      have hinf : N ⊓ L₀ = ⊥ := by
        rw [eq_bot_iff]
        intro y hy
        have hy' : (⟨y, hy.2⟩ : L₀) ∈ N.subgroupOf L₀ := hy.1
        rw [hbot, Subgroup.mem_bot] at hy'
        exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hy')
      have hcomm : ⁅N, L₀⁆ = ⊥ := le_bot_iff.mp (hinf ▸ Subgroup.commutator_le_inf N L₀)
      have hcent : N ≤ Subgroup.centralizer (L₀ : Set H) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hcomm
      rw [eq_bot_iff]
      intro c hc
      have hιc : ι c ∈ Subgroup.centralizer (pGammaL2PSLRange F : Set (PGammaL2 F)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [← hd.map_linearCore] at hy
        obtain ⟨l, hl, rfl⟩ := hy
        rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.mp (hcent hc)) l hl]
      rw [CFSG.GorensteinWalter.pGammaL2_pslRange_centralizer_eq_bot F hd.isOddPrimePower_card h3,
        Subgroup.mem_bot] at hιc
      exact (Subgroup.mem_bot).mpr (hd.injective (hιc.trans (map_one ι).symm))
    · intro y hy
      have hy' : (⟨y, hy⟩ : L₀) ∈ N.subgroupOf L₀ := by
        rw [htop]
        exact Subgroup.mem_top _
      exact hy'
  have hL₀D : (L₀ ⊔ D).Normal :=
    cr23_normal_of_commutator_le (hd.commutator_le_linearCore.trans le_sup_left)
  have hEx : E ≤ Subgroup.centralizer ({x} : Set H) := by
    intro e he
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.mp (hd.le_centralizer he)) x hx).symm
  have hK₀N : Subgroup.centralizer ({x} : Set H) ≤
      Subgroup.normalizer (pCoreIn p K₀ : Set H) := by
    intro g hg
    apply cr23_normalizer_le_normalizer_map (CFSG.pCore p K₀)
    apply Subgroup.inf_normalizer_le_normalizer_inf
    refine ⟨?_, Subgroup.le_normalizer hg⟩
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top g
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    have : IsCyclic E := hd.isCyclic
    exact congrArg Subtype.val ((IsCyclic.commGroup (α := E)).mul_comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hSPE : (S : Subgroup H) ≤ Subgroup.normalizer (PE : Set H) := by
    intro s hs
    apply cr23_mem_normalizer_of_mem_centralizer
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact ((Subgroup.mem_centralizer_iff.mp (hd.le_centralizer (hPE he))) s hs).symm
  have hEPE : E ≤ Subgroup.normalizer (PE : Set H) := by
    intro f hf
    apply cr23_mem_normalizer_of_mem_centralizer
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact hEcomm e (hPE he) f hf
  have hSN : (S : Subgroup H) ≤ Subgroup.normalizer (Ubar : Set H) :=
    (le_inf (hxS.trans hK₀N) hSPE).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hEN : E ≤ Subgroup.normalizer (Ubar : Set H) :=
    (le_inf (hEx.trans hK₀N) hEPE).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hSL : (S : Subgroup H) ≤ L := hd.sylow_le S
  have hL₀L : L₀ ≤ L := hd.linearCore_le
  have hLS : L ≤ L₀ ⊔ (S : Subgroup H) := by
    rcases hd.relIndex_linearCore with h1 | h2
    · exact (Subgroup.relIndex_eq_one.mp h1).trans le_sup_left
    · have hMle : L₀ ⊔ (S : Subgroup H) ≤ L := sup_le hL₀L hSL
      have hmul := Subgroup.relIndex_mul_relIndex L₀ (L₀ ⊔ (S : Subgroup H)) L le_sup_left hMle
      rw [h2] at hmul
      have hne : L₀.relIndex (L₀ ⊔ (S : Subgroup H)) ≠ 1 := by
        intro h1
        have hSL₀ : (S : Subgroup H) ≤ L₀ :=
          le_sup_right.trans (Subgroup.relIndex_eq_one.mp h1)
        have hidx := Subgroup.relIndex_mul_relIndex (S : Subgroup H) L₀ L hSL₀ hL₀L
        have hidx2 := Subgroup.relIndex_mul_index hSL
        apply S.not_dvd_index
        rw [← hidx2, ← hidx, h2]
        exact Dvd.dvd.mul_right (Dvd.intro_left _ rfl) _
      have h1 : (L₀ ⊔ (S : Subgroup H)).relIndex L = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp (Dvd.intro _ hmul) with h | h
        · exact absurd h hne
        · rw [h] at hmul
          omega
      exact Subgroup.relIndex_eq_one.mp h1
  apply top_le_iff.mp
  calc (⊤ : Subgroup H) = L ⊔ E := hd.sup_eq_top.symm
    _ ≤ L₀ ⊔ (S : Subgroup H) ⊔ E := sup_le_sup_right hLS _
    _ ≤ N ⊔ Subgroup.normalizer (Ubar : Set H) :=
        sup_le (sup_le (hL₀N.trans le_sup_left) (hSN.trans le_sup_right))
          (hEN.trans le_sup_right)

omit [Finite H] in
theorem sup_eq_top_of_mulEquiv_aSeven (e : H ≃* alternatingGroup (Fin 7)) (N : Subgroup H)
    [hN : N.Normal] (hN1 : N ≠ ⊥) (M : Subgroup H) : N ⊔ M = ⊤ := by
  have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by norm_num)
  have hs : IsSimpleGroup H := e.isSimpleGroup
  rcases hs.eq_bot_or_eq_top_of_normal N with h | h
  · exact absurd h hN1
  · rw [h, top_sup_eq]

end Linear

section Ambient

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem cr23_map_normalizer {Y : Subgroup G} (Q : Subgroup Y) :
    (Subgroup.normalizer (Q : Set Y)).map Y.subtype =
      Y ⊓ Subgroup.normalizer ((Q.map Y.subtype : Subgroup G) : Set G) := by
  have hle : Q.map Y.subtype ≤ Y := Subgroup.map_subtype_le Q
  have hQ : (Q.map Y.subtype).subgroupOf Y = Q :=
    Subgroup.comap_map_eq_self_of_injective Y.subtype_injective Q
  have h := Subgroup.subgroupOf_normalizer_eq hle
  rw [hQ] at h
  rw [← h, Subgroup.subgroupOf_map_subtype, inf_comm]

namespace Setting

variable (σ : Setting G)

@[expose] def LinearImageForm (r : ℕ) (K U : Subgroup G) : Prop :=
  ∀ hxK : σ.x ∈ K, ∀ S : Sylow 2 (K ⧸ CFSG.oddCore K),
    (σ.D.subgroupOf K).map (QuotientGroup.mk' (CFSG.oddCore K)) ≤ S →
    ∀ (F : Type) [Field F] [Finite F] (ι : K ⧸ CFSG.oddCore K →* PGammaL2 F)
      (L E : Subgroup (K ⧸ CFSG.oddCore K)), CFSG.ABGDGroups.IsLinearDecomposition ι L E S →
      (U.subgroupOf K).map (QuotientGroup.mk' (CFSG.oddCore K)) = ⊥ ∨
        (3 < Nat.card F ∧ ∃ PE ≤ E,
          (U.subgroupOf K).map (QuotientGroup.mk' (CFSG.oddCore K)) =
            pCoreIn r ((CFSG.ABGDGroups.linearCore ι ⊔
                (σ.D.subgroupOf K).map (QuotientGroup.mk' (CFSG.oddCore K))) ⊓
              Subgroup.centralizer
                ({QuotientGroup.mk' (CFSG.oddCore K) ⟨σ.x, hxK⟩} : Set (K ⧸ CFSG.oddCore K))) ⊔
              PE)

theorem claimR23_of_imageForm (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (hh : σ.height = 1)
    {r : ℕ} {K U : Subgroup G} (hDK : σ.D ≤ K) (hKD : IsDGroup K) (hUK : U ≤ K)
    (hform : σ.LinearImageForm r K U) (L : Subgroup G) (hOL : oddCoreIn K < L) (hLK : L ≤ K)
    (hKL : K ≤ Subgroup.normalizer (L : Set G)) :
    K ≤ L ⊔ (K ⊓ Subgroup.normalizer ((oddCoreIn K ⊔ U : Subgroup G) : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (CFSG.oddCore K) with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  set Ubar : Subgroup (K ⧸ CFSG.oddCore K) := (U.subgroupOf K).map π with hUbar
  have hxK : σ.x ∈ K := hDK (σ.T_le_D hσ σ.x_mem_T)
  obtain ⟨m, hSD⟩ : ∃ m, HasSemidihedralSylow G m := by
    rcases hσ.sylow with ⟨-, h⟩ | h
    · exact h
    · exact absurd h.1 (by rw [hh]; norm_num)
  have hW : ¬ ∃ n, HasWreathedSylow (K ⧸ CFSG.oddCore K) n := by
    rintro ⟨n, hn⟩
    rw [CFSG.ABGDGroups.hasWreathedSylow_quotient_oddCore_iff] at hn
    exact cr23_not_hasWreathedSylow hSD K n hn
  have hDp : IsPGroup 2 σ.D := σ.S.isPGroup'.to_le σ.D_le_S
  obtain ⟨SK, hSK⟩ := (hDp.comap_subtype (K := K)).exists_le_sylow
  obtain ⟨S₁, hS₁⟩ := (SK.isPGroup'.map K.subtype).exists_le_sylow
  have hDS₁ : σ.D ≤ (S₁ : Subgroup G) := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hDK]
    exact (Subgroup.map_mono hSK).trans hS₁
  have hxc := (hII.center_involution_of_sylow S₁ hDS₁).1
  set Sbar : Sylow 2 (K ⧸ CFSG.oddCore K) := SK.mapSurjective hπ with hSbar
  have hDS : (σ.D.subgroupOf K).map π ≤ (Sbar : Subgroup _) := by
    rw [hSbar, Sylow.coe_mapSurjective]
    exact Subgroup.map_mono hSK
  have hxD : (⟨σ.x, hxK⟩ : K) ∈ σ.D.subgroupOf K := σ.T_le_D hσ σ.x_mem_T
  have hxS : π ⟨σ.x, hxK⟩ ∈ (Sbar : Subgroup _) := hDS (Subgroup.mem_map_of_mem π hxD)
  have hSx : (Sbar : Subgroup (K ⧸ CFSG.oddCore K)) ≤
      Subgroup.centralizer ({π ⟨σ.x, hxK⟩} : Set (K ⧸ CFSG.oddCore K)) := by
    rw [hSbar, Sylow.coe_mapSurjective]
    rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hsS₁ : (s : G) ∈ (S₁ : Subgroup G) := hS₁ ⟨s, hs, rfl⟩
    exact ((Subgroup.mem_centralizer_iff.mp hxc.2) (s : G) hsS₁)
  have hclaim : ∀ (N : Subgroup (K ⧸ CFSG.oddCore K)) [N.Normal], N ≠ ⊥ →
      N ⊔ Subgroup.normalizer (Ubar : Set (K ⧸ CFSG.oddCore K)) = ⊤ := by
    intro N hN hN1
    rcases CFSG.ABGDGroups.aSeven_or_linearDecomposition
        (CFSG.ABGDGroups.isDGroup_quotient_oddCore hKD)
        (CFSG.LyonsUnitaryFour.oddCore_quotient_oddCore_eq_bot K) hW with he7 | hlin
    · obtain ⟨e⟩ := he7
      exact sup_eq_top_of_mulEquiv_aSeven e N hN1 _
    · obtain ⟨F, _, _, ι, L', E, hd⟩ := hlin Sbar
      rcases hform hxK Sbar hDS F ι L' E hd with hU1 | ⟨h3, PE, hPE, hUeq⟩
      · rw [show Ubar = ⊥ from hU1, Subgroup.normalizer_eq_top, sup_top_eq]
      · rw [show Ubar = _ from hUeq]
        exact sup_normalizer_eq_top_of_linearDecomposition hd h3 _ hxS hSx r hPE N hN1
  set L' : Subgroup K := L.subgroupOf K with hL'
  have hL'n : L'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLK).mpr hKL
  have hOL' : CFSG.oddCore K ≤ L' := by
    intro y hy
    exact hOL.le ⟨y, hy, rfl⟩
  have hN1 : L'.map π ≠ ⊥ := by
    intro hbot
    rw [Subgroup.map_eq_bot_iff, hπdef, QuotientGroup.ker_mk'] at hbot
    apply hOL.not_ge
    rw [← Subgroup.map_subgroupOf_eq_of_le hLK]
    exact Subgroup.map_mono hbot
  have hNn : (L'.map π).Normal := hL'n.map π hπ
  have htop := hclaim (L'.map π) hN1
  have hK' : (⊤ : Subgroup K) ≤ L' ⊔ Subgroup.normalizer
      ((CFSG.oddCore K ⊔ U.subgroupOf K : Subgroup K) : Set K) := by
    have h := congrArg (Subgroup.comap π) htop
    rw [← Subgroup.comap_sup_eq π _ _ hπ, Subgroup.comap_normalizer_eq_of_surjective _ hπ,
      hπdef, QuotientGroup.comap_map_mk', QuotientGroup.comap_map_mk', sup_eq_right.mpr hOL',
      Subgroup.comap_top] at h
    rw [h]
  have hmap := Subgroup.map_mono (f := K.subtype) hK'
  rw [Subgroup.map_sup, cr23_map_normalizer, Subgroup.map_sup,
    Subgroup.map_subgroupOf_eq_of_le hUK, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
    hL', Subgroup.map_subgroupOf_eq_of_le hLK] at hmap
  exact hmap

theorem claimR23_of_not_wreathed (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (hh : σ.height = 1)
    (h_c12 : ∀ J : Subgroup G, σ.IsV21Layer J → σ.HypIV7 σ.p → ∀ W ∈ σ.familyW J,
      ∀ P : Subgroup G, IsSylowOf σ.p P σ.C → σ.D ≤ Subgroup.normalizer (P : Set G) →
      ∀ K ∈ σ.familyMstar σ.p, W ≤ K →
      ∀ U ∈ maximals (signalizersPerm K σ.D W σ.p), U ∈ maximals (signalizers K σ.D σ.p) →
      P ≤ U → pPrimeCoreIn σ.p (U ⊔ W) = ⊥ → σ.LinearImageForm σ.p K U) :
    ∀ J : Subgroup G, σ.IsV21Layer J → σ.HypIV7 σ.p → ∀ W ∈ σ.familyW J,
      ∀ P : Subgroup G, IsSylowOf σ.p P σ.C → σ.D ≤ Subgroup.normalizer (P : Set G) →
      ∀ K ∈ σ.familyMstar σ.p, W ≤ K →
      ∀ U ∈ maximals (signalizersPerm K σ.D W σ.p), U ∈ maximals (signalizers K σ.D σ.p) →
      P ≤ U → pPrimeCoreIn σ.p (U ⊔ W) = ⊥ →
      ∀ L : Subgroup G, oddCoreIn K < L → L ≤ K → K ≤ Subgroup.normalizer (L : Set G) →
        K ≤ L ⊔ (K ⊓ Subgroup.normalizer ((oddCoreIn K ⊔ U : Subgroup G) : Set G)) := by
  intro J hJ hHyp W hW P hP hDP K hK hWK U hU1 hU2 hPU hUW L hOL hLK hKL
  exact σ.claimR23_of_imageForm hσ hII hh hK.2.1 hK.2.2.1.1 hU2.1.1
    (h_c12 J hJ hHyp W hW P hP hDP K hK hWK U hU1 hU2 hPU hUW) L hOL hLK hKL

theorem propR2Input_of_height_one (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (hh : σ.height = 1)
    (h91 : σ.PropIV91)
    (h_II61D : ∀ H : Subgroup G, σ.D ≤ H → IsDGroupWrt (σ.T.subgroupOf H) → ∀ r : ℕ, r.Prime →
      r ≠ 2 → CFSG.pCore r H ≠ ⊥ → CFSG.pPrimeCore r H ≤ CFSG.oddCore H → IsPStable r H)
    (h_c12 : ∀ J : Subgroup G, σ.IsV21Layer J → σ.HypIV7 σ.p → ∀ W ∈ σ.familyW J,
      ∀ P : Subgroup G, IsSylowOf σ.p P σ.C → σ.D ≤ Subgroup.normalizer (P : Set G) →
      ∀ K ∈ σ.familyMstar σ.p, W ≤ K →
      ∀ U ∈ maximals (signalizersPerm K σ.D W σ.p), U ∈ maximals (signalizers K σ.D σ.p) →
      P ≤ U → pPrimeCoreIn σ.p (U ⊔ W) = ⊥ → σ.LinearImageForm σ.p K U) :
    ∀ J : Subgroup G, σ.IsV21Layer J → V56.PropR2Input σ J :=
  σ.propR2Input_of hσ h91 h_II61D (σ.claimR23_of_not_wreathed hσ hII hh h_c12)

end Setting

end Ambient


end CFSG.ABGTheoremB
