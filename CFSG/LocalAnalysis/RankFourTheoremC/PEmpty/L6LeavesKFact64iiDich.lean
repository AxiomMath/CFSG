module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact64iiComp
import CFSG.RankThree.PartOne.D4RC.Burnside

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKF64ii

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.GH74.Uniqueness.SU Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Asm

variable {Z : Type} [Group Z] [Finite Z] {p : ℕ}

namespace Ctx

variable {S : Sylow p Z} {x z : Z} {M : Subgroup Z} (h : Ctx p S x z M)

include h

theorem orderOf_conjAut (hI121 : KFact64iiI121) {K : Subgroup Z} (hK : IsComponentOf K ⊤)
    {y : Z} (hyB : y ∈ zpowers x ⊔ zpowers z)
    (hout : conjAut K y (h.plane_le_normalizer hI121 hK hyB) ∉
      (MulAut.conj : ↥K →* MulAut ↥K).range) :
    orderOf (conjAut K y (h.plane_le_normalizer hI121 hK hyB)) = p := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hφ1 : conjAut K y (h.plane_le_normalizer hI121 hK hyB) ≠ 1 := fun h1 =>
    hout ⟨1, by rw [h1]; simp⟩
  have hφp : conjAut K y (h.plane_le_normalizer hI121 hK hyB) ^ p = 1 := by
    refine MulEquiv.ext fun g => Subtype.ext ?_
    rw [conjAut_pow, h.plane_pow y hyB]
    simp
  exact orderOf_eq_prime hφp hφ1

theorem z_mem_of_outer (hOuter : KFact64iiOuterSylow) (hI121 : KFact64iiI121)
    {K : Subgroup Z} (hK : IsComponentOf K ⊤) {y : Z} (hyB : y ∈ zpowers x ⊔ zpowers z)
    (hyK : y ∉ K)
    (hout : conjAut K y (h.plane_le_normalizer hI121 hK hyB) ∉
      (MulAut.conj : ↥K →* MulAut ↥K).range) : z ∈ K := by
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  set hy := h.plane_le_normalizer hI121 hK hyB with hhy
  have hyp : y ^ p = 1 := h.plane_pow y hyB
  have hy1 : y ≠ 1 := fun h1 => hyK (h1 ▸ K.one_mem)
  have hyo : orderOf y = p := orderOf_eq_prime hyp hy1
  have hord := h.orderOf_conjAut hI121 hK hyB hout
  obtain ⟨hs1, hs2⟩ := h.isSimpleGroup_component hK
  have hcat := h.isCatalog_component hK
  obtain ⟨P, hP⟩ := h.exists_sylow_component hK
  obtain ⟨r, hrP, hrφ⟩ := hOuter p hp h.three_le ↥K hs1 hs2 hcat (h.pRank_top_component hI121 hK)
    _ hord hout P
  have hrSK : (r : Z) ∈ (S : Subgroup Z) ⊓ K := by
    rw [← hP]
    exact ⟨r, hrP, rfl⟩
  have hrK : (r : Z) ∈ K := r.2
  have hyne : y * (r : Z) * y⁻¹ ≠ (r : Z) := fun heq =>
    hrφ (Subtype.ext ((conjAut_apply K y hy r).trans heq))
  have hrN : (r : Z) ∈ normalizer ((zpowers x ⊔ zpowers z : Subgroup Z) : Set Z) :=
    h.S_le_normalizer_plane hrSK.1
  have hrz : (r : Z) * z * (r : Z)⁻¹ ∈ zpowers z :=
    (mem_normalizer_iff.mp (h.NB hrN) z).mp (mem_zpowers z)
  obtain ⟨a, haK, haS, hao, hBK⟩ := h.exists_inf_plane hI121 hK
  have haB : a ∈ (zpowers x ⊔ zpowers z) ⊓ K := hBK ▸ mem_zpowers a
  have hap : a ^ p = 1 := by
    have := pow_orderOf_eq_one a
    rwa [hao] at this
  have ha1 : a ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hao
    exact hp.one_lt.ne hao
  have huB : (r : Z) * y * (r : Z)⁻¹ ∈ zpowers x ⊔ zpowers z := by
    refine h.omega _ ((S : Subgroup Z).mul_mem ((S : Subgroup Z).mul_mem hrSK.1
      (h.plane_le hyB)) ((S : Subgroup Z).inv_mem hrSK.1)) ?_
    rw [conj_pow, hyp]
    simp
  set c : Z := (r : Z) * y * (r : Z)⁻¹ * y⁻¹ with hc
  have hcB : c ∈ zpowers x ⊔ zpowers z := (zpowers x ⊔ zpowers z).mul_mem huB
    ((zpowers x ⊔ zpowers z).inv_mem hyB)
  have hcK : c ∈ K := by
    have e : c = (r : Z) * (y * (r : Z)⁻¹ * y⁻¹) := by rw [hc]; group
    rw [e]
    exact K.mul_mem hrK ((mem_normalizer_iff.mp hy (r : Z)⁻¹).mp (K.inv_mem hrK))
  have hc1 : c ≠ 1 := by
    intro h1
    apply hyne
    have h2 : (r : Z) * y * (r : Z)⁻¹ = y := mul_inv_eq_one.mp h1
    have h3 : (r : Z) * y = y * (r : Z) := mul_inv_eq_iff_eq_mul.mp h2
    exact mul_inv_eq_iff_eq_mul.mpr h3.symm
  have hcz : c ∈ zpowers a := hBK ▸ (⟨hcB, hcK⟩ : c ∈ (zpowers x ⊔ zpowers z) ⊓ K)
  have hra : (r : Z) * a * (r : Z)⁻¹ = a := by
    have haSK : a ∈ (S : Subgroup Z) ⊓ K := ⟨haS, haK⟩
    rw [← hP] at haSK
    obtain ⟨a', ha'P, rfl⟩ := haSK
    have := h.abelian_sylow_component hK P hP r hrP a' ha'P
    have h2 : ((r * a' : ↥K) : Z) = ((a' * r : ↥K) : Z) := congrArg Subtype.val this
    simp only [Subgroup.coe_mul] at h2
    exact mul_inv_eq_iff_eq_mul.mpr h2
  have hry : (r : Z) * y * (r : Z)⁻¹ = c * y := by
    rw [hc]
    group
  have hya : y ∉ zpowers a := fun hmem => hyK ((zpowers_le.mpr haK) hmem)
  have hay : a * y = y * a := h.plane_comm a haB.1 y hyB
  obtain ⟨-, hcard⟩ := SU1.isElemAbelian_card_sup_zpowers hp hap hyp ha1 hya hay
  have hAYB : zpowers a ⊔ zpowers y ≤ zpowers x ⊔ zpowers z :=
    sup_le (zpowers_le.mpr haB.1) (zpowers_le.mpr hyB)
  have hAYeq : zpowers a ⊔ zpowers y = zpowers x ⊔ zpowers z :=
    Subgroup.eq_of_le_of_card_ge hAYB (by rw [hcard, h.card_plane])
  have hzB : z ∈ zpowers a ⊔ zpowers y := by
    rw [hAYeq]
    exact mem_sup_right (mem_zpowers z)
  have hza : z ∈ zpowers a :=
    transvection_aux hp hao hyo h.z_order hay hzB hra hry hcz hc1 hrz
  exact (zpowers_le.mpr haK) hza

theorem exists_centralizing_of_inner (hI121 : KFact64iiI121) {K : Subgroup Z}
    (hK : IsComponentOf K ⊤) {y : Z} (hyB : y ∈ zpowers x ⊔ zpowers z) (hyK : y ∉ K)
    (hin : conjAut K y (h.plane_le_normalizer hI121 hK hyB) ∈
      (MulAut.conj : ↥K →* MulAut ↥K).range) :
    ∃ y₁ ∈ zpowers x ⊔ zpowers z, y₁ ∉ K ∧ ∀ g ∈ K, y₁ * g = g * y₁ := by
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  set hy := h.plane_le_normalizer hI121 hK hyB with hhy
  obtain ⟨k, hk⟩ := hin
  have hky : ∀ g : ↥K, ((k : Z)) * (g : Z) * (k : Z)⁻¹ = y * (g : Z) * y⁻¹ := by
    intro g
    have h1 := congrArg (fun φ : MulAut ↥K => ((φ g : ↥K) : Z)) hk
    simpa [conjAut_apply] using h1
  have hyp : y ^ p = 1 := h.plane_pow y hyB
  obtain ⟨a, haK, haS, hao, hBK⟩ := h.exists_inf_plane hI121 hK
  have haB : a ∈ (zpowers x ⊔ zpowers z) ⊓ K := hBK ▸ mem_zpowers a
  have hap : a ^ p = 1 := by
    have := pow_orderOf_eq_one a
    rwa [hao] at this
  have ha1 : a ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hao
    exact hp.one_lt.ne hao
  have hkcomm : a * (k : Z) = (k : Z) * a := by
    have h1 := hky ⟨a, haK⟩
    have h2 : y * a * y⁻¹ = a := mul_inv_eq_iff_eq_mul.mpr (h.plane_comm y hyB a haB.1)
    rw [h2] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  have hkp : k ^ p = 1 := by
    have hφp : conjAut K y hy ^ p = 1 := by
      refine MulEquiv.ext fun g => Subtype.ext ?_
      rw [conjAut_pow, hyp]
      simp
    have h2 : ((MulAut.conj : ↥K →* MulAut ↥K) k) ^ p = 1 := by rw [hk]; exact hφp
    have h3 : (MulAut.conj : ↥K →* MulAut ↥K) (k ^ p) = 1 := by rw [map_pow]; exact h2
    have hmem : k ^ p ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h4 := congrArg (fun φ : MulAut ↥K => φ g) h3
      simp only [MulAut.conj_apply, MulAut.one_apply] at h4
      exact (mul_inv_eq_iff_eq_mul.mp h4).symm
    rw [h.center_component_eq_bot hK, Subgroup.mem_bot] at hmem
    exact hmem
  have hkpZ : (k : Z) ^ p = 1 := by simpa using congrArg Subtype.val hkp
  have hkB : (k : Z) ∈ zpowers a := by
    by_contra hkn
    obtain ⟨-, hcard⟩ := SU1.isElemAbelian_card_sup_zpowers hp hap hkpZ ha1 hkn hkcomm
    have hle : zpowers a ⊔ zpowers (k : Z) ≤ K :=
      sup_le (zpowers_le.mpr haK) (zpowers_le.mpr k.2)
    have hel := (SU1.isElemAbelian_card_sup_zpowers hp hap hkpZ ha1 hkn hkcomm).1
    have h2 : 2 ≤ Open.pRank p K := SU1.le_pRank hp.one_lt hle hel (k := 2) hcard
    have := h.pRank_component_le_one hI121 hK
    omega
  have hkB' : (k : Z) ∈ zpowers x ⊔ zpowers z := (zpowers_le.mpr haB.1) hkB
  refine ⟨(k : Z)⁻¹ * y, (zpowers x ⊔ zpowers z).mul_mem
    ((zpowers x ⊔ zpowers z).inv_mem hkB') hyB, ?_, ?_⟩
  · intro hmem
    apply hyK
    have : (k : Z) * ((k : Z)⁻¹ * y) ∈ K := K.mul_mem k.2 hmem
    simpa using this
  · intro g hg
    have h1 := hky ⟨g, hg⟩
    calc (k : Z)⁻¹ * y * g = (k : Z)⁻¹ * (y * g * y⁻¹) * y := by group
      _ = (k : Z)⁻¹ * ((k : Z) * g * (k : Z)⁻¹) * y := by rw [h1]
      _ = g * ((k : Z)⁻¹ * y) := by group

theorem z_mem_or_of_centralizing (hI121 : KFact64iiI121) {K : Subgroup Z}
    (hK : IsComponentOf K ⊤) {y₁ : Z} (hy₁B : y₁ ∈ zpowers x ⊔ zpowers z) (hy₁K : y₁ ∉ K)
    (hy₁c : ∀ g ∈ K, y₁ * g = g * y₁) : z ∈ K ∨ zpowers z = zpowers y₁ := by
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP⟩ := h.exists_sylow_component hK
  have hcyc := h.isCyclic_sylow_component hI121 hK P hP
  have hP1 : (P : Subgroup ↥K) ≠ ⊥ := fun h0 => P.not_dvd_index (by
    rw [h0, Subgroup.index_bot]
    exact dvd_card_of_isComponentOf hp h.core hK)
  have hperf : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = ⊤ := hK.2.2.1
  obtain ⟨g, hgN, a, haP, hap, hga⟩ :=
    CFSG.RankThree.PartOne.D4RC.rcb_exists_normalizer_elt_perfect hperf P.isPGroup'
      P.not_dvd_index hcyc hP1
  have haSK : (a : Z) ∈ (S : Subgroup Z) ⊓ K := hP ▸ ⟨a, haP, rfl⟩
  have hgaP : g * a * g⁻¹ ∈ (P : Subgroup ↥K) := (mem_normalizer_iff.mp hgN a).mp haP
  have hga' : (g : Z) * (a : Z) * (g : Z)⁻¹ ∈ (S : Subgroup Z) ⊓ K := hP ▸ ⟨_, hgaP, rfl⟩
  have haz : (a : Z) ^ p = 1 := by simpa using congrArg Subtype.val hap
  have hgaz : ((g : Z) * (a : Z) * (g : Z)⁻¹) ^ p = 1 := by
    rw [conj_pow, haz]
    simp
  have hne : (g : Z) * (a : Z) * (g : Z)⁻¹ ≠ (a : Z) := fun h' => hga (Subtype.ext h')
  have ha1 : (a : Z) ≠ 1 := fun h1 => hne (by rw [h1]; simp)
  have hao : orderOf (a : Z) = p := orderOf_eq_prime haz ha1
  have haB : (a : Z) ∈ zpowers x ⊔ zpowers z := h.omega _ haSK.1 haz
  have haK : (a : Z) ∈ K := a.2
  obtain ⟨a₀, ha₀K, ha₀S, ha₀o, hBK⟩ := h.exists_inf_plane hI121 hK
  have hzBK : zpowers (a : Z) = (zpowers x ⊔ zpowers z) ⊓ K := by
    have hmem : (a : Z) ∈ (zpowers x ⊔ zpowers z) ⊓ K := ⟨haB, haK⟩
    rw [hBK] at hmem ⊢
    exact L6LeavesNS.zpowers_eq_of_mem_of_ne_one hp ha₀o hmem ha1
  have hgaB : (g : Z) * (a : Z) * (g : Z)⁻¹ ∈ zpowers (a : Z) := by
    rw [hzBK]
    exact ⟨h.omega _ hga'.1 hgaz, hga'.2⟩
  have hy₁p : y₁ ^ p = 1 := h.plane_pow y₁ hy₁B
  have hy₁1 : y₁ ≠ 1 := fun h1 => hy₁K (h1 ▸ K.one_mem)
  have hy₁o : orderOf y₁ = p := orderOf_eq_prime hy₁p hy₁1
  have hy₁a : y₁ * (a : Z) = (a : Z) * y₁ := h.plane_comm y₁ hy₁B a haB
  have hgy : (g : Z) * y₁ * (g : Z)⁻¹ = y₁ :=
    mul_inv_eq_iff_eq_mul.mpr (hy₁c g g.2).symm
  have hay : (a : Z) ∉ zpowers y₁ := by
    intro hmem
    apply hy₁K
    have heq : zpowers (a : Z) = zpowers y₁ :=
      L6LeavesNS.zpowers_eq_of_mem_of_ne_one hp hy₁o hmem ha1
    have : y₁ ∈ zpowers (a : Z) := by
      rw [heq]
      exact mem_zpowers y₁
    exact (zpowers_le.mpr haK) this
  obtain ⟨-, hcard⟩ := SU1.isElemAbelian_card_sup_zpowers hp hy₁p haz hy₁1 hay hy₁a
  have hY₁B : zpowers y₁ ⊔ zpowers (a : Z) ≤ zpowers x ⊔ zpowers z :=
    sup_le (zpowers_le.mpr hy₁B) (zpowers_le.mpr haB)
  have hBeq : zpowers y₁ ⊔ zpowers (a : Z) = zpowers x ⊔ zpowers z :=
    Subgroup.eq_of_le_of_card_ge hY₁B (by rw [hcard, h.card_plane])
  have hgB : (g : Z) ∈ normalizer ((zpowers x ⊔ zpowers z : Subgroup Z) : Set Z) := by
    refine L6LeavesNS.mem_normalizer_of_map_conj_le ?_
    rw [← hBeq, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
    · have : (MulAut.conj (g : Z)).toMonoidHom y₁ = y₁ := hgy
      rw [this]
      exact mem_sup_left (mem_zpowers y₁)
    · have : (MulAut.conj (g : Z)).toMonoidHom (a : Z) ∈ zpowers (a : Z) := hgaB
      exact mem_sup_right this
  have hgz : (g : Z) * z * (g : Z)⁻¹ ∈ zpowers z :=
    (mem_normalizer_iff.mp (h.NB hgB) z).mp (mem_zpowers z)
  by_cases hy₁z : y₁ ∈ zpowers z
  · exact Or.inr (L6LeavesNS.zpowers_eq_of_mem_of_ne_one hp h.z_order hy₁z hy₁1).symm
  · left
    have hzB : z ∈ zpowers y₁ ⊔ zpowers (a : Z) := by
      rw [hBeq]
      exact mem_sup_right (mem_zpowers z)
    exact (zpowers_le.mpr haK)
      (L6LeavesNS.lines_aux hp hy₁o hao h.z_order hy₁a hzB hgy hgaB hne hgz hy₁z)

theorem z_mem_or (hOuter : KFact64iiOuterSylow) (hI121 : KFact64iiI121) {K : Subgroup Z}
    (hK : IsComponentOf K ⊤) :
    z ∈ K ∨ ∃ y₁ ∈ zpowers x ⊔ zpowers z, y₁ ∉ K ∧ (∀ g ∈ K, y₁ * g = g * y₁) ∧
      zpowers z = zpowers y₁ := by
  obtain ⟨y, hyB, hyK⟩ : ∃ y ∈ zpowers x ⊔ zpowers z, y ∉ K := by
    by_contra hcon
    push Not at hcon
    exact h.not_plane_le hI121 hK fun y hy => hcon y hy
  by_cases hin : conjAut K y (h.plane_le_normalizer hI121 hK hyB) ∈
      (MulAut.conj : ↥K →* MulAut ↥K).range
  · obtain ⟨y₁, hy₁B, hy₁K, hy₁c⟩ := h.exists_centralizing_of_inner hI121 hK hyB hyK hin
    rcases h.z_mem_or_of_centralizing hI121 hK hy₁B hy₁K hy₁c with hz | hz
    · exact Or.inl hz
    · exact Or.inr ⟨y₁, hy₁B, hy₁K, hy₁c, hz⟩
  · exact Or.inl (h.z_mem_of_outer hOuter hI121 hK hyB hyK hin)

theorem exists_b (hI121 : KFact64iiI121) {K : Subgroup Z} (hK : IsComponentOf K ⊤)
    (hzK : z ∈ K) :
    ∃ b ∈ zpowers x ⊔ zpowers z, b ∉ zpowers z ∧
      ((∀ g ∈ K, b * g = g * b) ∨ OuterAction p K b) := by
  obtain ⟨y, hyB, hyK⟩ : ∃ y ∈ zpowers x ⊔ zpowers z, y ∉ K := by
    by_contra hcon
    push Not at hcon
    exact h.not_plane_le hI121 hK fun y hy => hcon y hy
  have hzle : zpowers z ≤ K := zpowers_le.mpr hzK
  by_cases hin : conjAut K y (h.plane_le_normalizer hI121 hK hyB) ∈
      (MulAut.conj : ↥K →* MulAut ↥K).range
  · obtain ⟨y₁, hy₁B, hy₁K, hy₁c⟩ := h.exists_centralizing_of_inner hI121 hK hyB hyK hin
    exact ⟨y₁, hy₁B, fun hmem => hy₁K (hzle hmem), Or.inl hy₁c⟩
  · exact ⟨y, hyB, fun hmem => hyK (hzle hmem),
      Or.inr ⟨h.plane_le_normalizer hI121 hK hyB, h.orderOf_conjAut hI121 hK hyB hin, hin⟩⟩

end Ctx

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKF64ii
