module

public import CFSG.LocalAnalysis.RankThreeUC.GN15LayerFinal
public import CFSG.LocalAnalysis.RankThreeUC.GN15CoverChief
public import CFSG.LocalAnalysis.RankThreeUC.GN15CoverS3
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedBasic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.AGLEmbeddingD2 CFSG.AGLEmbedding
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound CFSG.AGLEmbeddingD2.Tits.MsidePrelim
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open scoped Pointwise commutatorElement

section Generic

variable {Y : Type*} [Group Y]

theorem mem_of_mem_sup_of_pow_mem {K T : Subgroup Y} (hK : K.Normal) (hT : IsPGroup 2 T) {y : Y}
    (hy : y ∈ K ⊔ T) {k : ℕ} (hk : y ^ 3 ^ k ∈ K) : y ∈ K := by
  obtain ⟨l, hl, t, ht, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hy
  obtain ⟨j, hj⟩ := hT ⟨t, ht⟩
  have htj : t ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  set π : Y →* Y ⧸ K := QuotientGroup.mk' K with hπ
  have hl1 : π l = 1 := (QuotientGroup.eq_one_iff l).2 hl
  have h1 : orderOf (π (l * t)) ∣ 2 ^ j := by
    apply orderOf_dvd_of_pow_eq_one
    rw [map_mul, hl1, one_mul, ← map_pow, htj, map_one]
  have h2 : orderOf (π (l * t)) ∣ 3 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).2 hk
  have hcop : Nat.Coprime (2 ^ j) (3 ^ k) := Nat.Coprime.pow j k (by norm_num)
  have h3 : orderOf (π (l * t)) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have h4 : π (l * t) = 1 := orderOf_eq_one_iff.1 h3
  exact (QuotientGroup.eq_one_iff _).1 h4

theorem pow_mul_mem_of_pow_mem {B : Subgroup Y} (hB : B.Normal) {p b : Y} (hb : b ∈ B) {n : ℕ}
    (h : p ^ n ∈ B) : (p * b) ^ n ∈ B := by
  set π : Y →* Y ⧸ B := QuotientGroup.mk' B with hπ
  have hb1 : π b = 1 := (QuotientGroup.eq_one_iff b).2 hb
  have hp1 : π p ^ n = 1 := by rw [← map_pow]; exact (QuotientGroup.eq_one_iff _).2 h
  refine (QuotientGroup.eq_one_iff _).1 ?_
  show π ((p * b) ^ n) = 1
  rw [map_pow, map_mul, hb1, mul_one, hp1]

theorem exists_three_part [Finite Y] (h : Y) :
    ∃ m : ℕ, m % 3 = 1 ∧ ∃ k : ℕ, orderOf (h ^ m) = 3 ^ k := by
  obtain ⟨e, m', hm', hem⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos h).ne' 3 (by norm_num)
  refine ⟨m' * m', ?_, ?_⟩
  · have h12 : m' % 3 = 1 ∨ m' % 3 = 2 := by omega
    rcases h12 with h1 | h1 <;> simp [Nat.mul_mod, h1]
  · have hdvd : orderOf (h ^ (m' * m')) ∣ 3 ^ e := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← pow_mul]
      have : m' * m' * 3 ^ e = orderOf h * m' := by rw [hem]; ring
      rw [this, pow_mul, pow_orderOf_eq_one, one_pow]
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    exact ⟨k, hk⟩

omit [Group Y] in
private theorem mem_normalizer_of_normal'' {Z : Type*} [Group Z] {B : Subgroup Z} (hB : B.Normal)
    (g : Z) : g ∈ Subgroup.normalizer (B : Set Z) := by
  rw [Subgroup.normalizer_eq_top_iff.mpr hB]
  exact Subgroup.mem_top g

end Generic

section Layer

variable {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}

private theorem charTwo_sup_of_normal' (hX : GNSetting X T) (K : Subgroup X) : CharTwo (K ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQT : pCoreOf 2 (⊤ : Subgroup X) ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf hX.sylow
  have hQnormal : (pCoreOf 2 (⊤ : Subgroup X)).Normal := by
    rw [B6.pCoreOf_top]; infer_instance
  have hQn : (K ⊔ T) ≤ Subgroup.normalizer ((pCoreOf 2 (⊤ : Subgroup X) : Subgroup X) : Set X) :=
    fun g _ => (Subgroup.normalizer_eq_top_iff.mpr hQnormal).symm ▸ Subgroup.mem_top g
  have hQM : pCoreOf 2 (⊤ : Subgroup X) ≤ pCoreOf 2 (K ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hQT.trans le_sup_right) hQn
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  intro x hx
  exact hQM (hX.charTwo ⟨Subgroup.mem_top x, Subgroup.centralizer_le hQM hx.2⟩)

omit [Finite X] in
private theorem isSubnormal_inf_normal' {A B N : Subgroup X} (h : IsSubnormal A B) (hNB : N ≤ B)
    (hN : (N.subgroupOf B).Normal) : IsSubnormal (A ⊓ N) N := by
  induction h with
  | refl A =>
    rw [inf_eq_right.mpr hNB]
    exact IsSubnormal.refl _
  | step hAM hn _ ih =>
    refine IsSubnormal.step (inf_le_inf_right N hAM) ?_ (ih hNB hN)
    rw [Subgroup.normal_subgroupOf_iff hAM] at hn
    rw [Subgroup.normal_subgroupOf_iff (inf_le_inf_right N hAM)]
    intro x g hx hg
    exact ⟨hn x g hx.1 hg.1, N.mul_mem (N.mul_mem hg.2 hx.2) (N.inv_mem hg.2)⟩

omit [Finite X] in
private theorem isSubnormal_top_of_le' {K Y : Subgroup X} (hK : K.Normal)
    (hY : IsSubnormal Y (K ⊔ T)) (hYK : Y ≤ K) : IsSubnormal Y ⊤ := by
  have h1 : IsSubnormal (Y ⊓ K) K := isSubnormal_inf_normal' hY le_sup_left (hK.subgroupOf _)
  rw [inf_eq_left.2 hYK] at h1
  exact h1.trans (IsSubnormal.step le_top (hK.subgroupOf _) (IsSubnormal.refl _))

private theorem s3Factor_covered_rel' (hX : GNSetting X T) (hP : IsC118Pair T T₁ T₂)
    {K : Subgroup X} (hK : K.Normal)
    (hU : IsElemAbelian 2 (conjClosure (quasithinOmegaOneCenter T) (K ⊔ T)))
    (I : Finset (Subgroup (MulAut (IntMod (conjClosure (quasithinOmegaOneCenter T) (K ⊔ T)) hU))))
    (hMN : K ⊔ T ≤ Subgroup.normalizer
      ((conjClosure (quasithinOmegaOneCenter T) (K ⊔ T) : Subgroup X) : Set X))
    (hcard : ∀ L ∈ I, Nat.card L = 6)
    (hJM : autI hU (thompsonJ (K ⊔ T)) = ⨆ L ∈ I, L)
    (hSyl : IsSylowTwoOf (autI hU (thompsonJ T)) (autI hU (thompsonJ (K ⊔ T))))
    (hperm : ∀ g ∈ autI hU (K ⊔ T), ∀ L ∈ I, B1.conjAut g L ∈ I) (hfam : S3Family I) :
    ∀ L ∈ I, ∃ H₀ : Subgroup X, H₀ ≤ K ⊔ T ∧ L ≤ autI hU H₀ ∧
      (H₀ ≤ Subgroup.centralizer (T₁ : Set X) ∨ H₀ ≤ Subgroup.normalizer (T₂ : Set X)) := by
  intro L hL
  have hSylM : IsSylowTwoOf T (K ⊔ T) := B6.isSylowTwoOf_mono hX.sylow le_sup_right le_top
  obtain ⟨H₀, hHM, hHL, -, hGcl, hblock⟩ := ffGroupStepGen (charTwo_sup_of_normal' hX K) hSylM hU I
    hMN hcard hJM hSyl hperm hfam L hL
  refine ⟨H₀, hHM, hHL, ?_⟩
  obtain ⟨-, h1Z, -, -, h2B, -, hall⟩ := hP
  have hC₁B : T₁ ≤ baum T := h1Z.trans (C1GN.omegaOneCenterOf_le_baum T)
  have hd := hall X H₀ (baum T).subtype (baum T).subtype_injective
    (by rwa [Subgroup.range_subtype])
  rw [Subgroup.map_subgroupOf_eq_of_le hC₁B, Subgroup.map_subgroupOf_eq_of_le h2B] at hd
  rcases hd with h | h | h
  · left
    intro x hx
    exact Subgroup.mem_centralizer_iff.2 fun c hc =>
      ((Subgroup.mem_centralizer_iff.1 (h hc).2 x hx)).symm
  · exact Or.inr h
  · exfalso
    obtain ⟨Y, hYM, hYs, hYX⟩ := hblock h
    have hYK : Y ≤ K := CFSG.QuasithinUnique.Vol2Native.L239.le_of_isShort2_of_le_sup hX.sylow.2.1
      (Subgroup.normalizer_eq_top_iff.mpr hK ▸ le_top) hYX.1 hYM
    exact hX.noXBlock Y (isSubnormal_top_of_le' hK hYs hYK) hYX


end Layer

section Main

variable {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}

theorem cover_cases_of_le_gnKThree (hI59 : AGL81I59) (hX : GNSetting X T)
    (hP : IsC118Pair T T₁ T₂) {A B : Subgroup X} (hA : A.Normal) (hB : B.Normal) (hBA : B ≤ A)
    (hCB : gnC T ≤ B) (hAK : A ≤ gnKThree T)
    (hchief : ∀ D : Subgroup X, D.Normal → B ≤ D → D ≤ A → D = B ∨ D = A) :
    (∀ a ∈ A, ∃ k : ℕ, a ^ 2 ^ k ∈ B) ∨ ⁅A, thompsonJ T⁆ ≤ B ∨
      ((∀ a ∈ A, ∃ k : ℕ, a ^ 3 ^ k ∈ B) ∧ ∃ x ∈ A, x ∉ B ∧ (∃ k : ℕ, orderOf x = 3 ^ k) ∧
        (x ∈ Subgroup.centralizer (T₁ : Set X) ∨ x ∈ Subgroup.normalizer (T₂ : Set X))) := by
  classical
  obtain ⟨-, h1Z, -, -, h2B, h2c, hall⟩ := id hP
  have hK₃n : (gnKThree T).Normal := gnKThree_normal
  set K₃ : Subgroup X := gnKThree T with hK₃def
  set M : Subgroup X := K₃ ⊔ T with hMdef
  have hK₃M : K₃ ≤ M := le_sup_left
  have hTM : T ≤ M := le_sup_right
  have hAM : A ≤ M := hAK.trans hK₃M
  have hSylM : IsSylowTwoOf T M := B6.isSylowTwoOf_mono hX.sylow hTM le_top
  have hFM : CharTwo M := charTwo_sup_of_normal' hX K₃
  obtain ⟨-, hU, hred⟩ := conjClosure_isTwoReducedIn_of_charTwo hSylM hFM (le_refl _)
  set V : Subgroup X := conjClosure (quasithinOmegaOneCenter T) M with hVdef
  have hMN : M ≤ Subgroup.normalizer (V : Set X) := hred.2.1
  have hker : K₃ ⊓ Subgroup.centralizer (V : Set X) ≤ gnC T :=
    inf_centralizer_conjClosure_le hX hK₃n gnKThree_le_gnHPre
  by_cases hJV : thompsonJ T ≤ Subgroup.centralizer (V : Set X)
  · right; left
    rw [Subgroup.commutator_le]
    intro a ha j hj
    have haN : a ∈ Subgroup.normalizer (Subgroup.centralizer (V : Set X) : Set X) :=
      CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup V (hMN (hAM ha))
    have hjc : j ∈ Subgroup.centralizer (V : Set X) := hJV hj
    have h1 : a * j * a⁻¹ ∈ Subgroup.centralizer (V : Set X) :=
      (Subgroup.mem_normalizer_iff.mp haN j).mp hjc
    have hcc : ⁅a, j⁆ ∈ Subgroup.centralizer (V : Set X) := by
      rw [commutatorElement_def]
      exact mul_mem h1 (inv_mem hjc)
    have hcA : ⁅a, j⁆ ∈ A := by
      have : ⁅a, j⁆ = a * (j * a⁻¹ * j⁻¹) := by rw [commutatorElement_def]; group
      rw [this]
      exact A.mul_mem ha (hA.conj_mem _ (A.inv_mem ha) j)
    exact hCB (hker ⟨hAK hcA, hcc⟩)
  · have hFC := hI59 X M T V (CFSG.Open.IsKGroup.subgroup
      (CFSG.KCore.KGroupAllSimple.kGroupNonab hX.kGroup) M) hFM hSylM rfl
      (isPConstrained_three_autOn_gnKThree hX) hJV
    obtain ⟨hU', hred', I, hSyl, hJM, hcomm, hindep, hnat, htop, -, hinter, hperm⟩ := hFC
    have hfam : S3Fam I := ⟨hcomm, hindep, fun L hL => by
      obtain ⟨e, -, -⟩ := hnat L hL
      exact ⟨e⟩⟩
    have hcard : ∀ L ∈ I, Nat.card L = 6 := fun L hL => by
      obtain ⟨e, -, -⟩ := hnat L hL
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Quasithin.B69.card_sl2
    have hfamR : S3Family I := ⟨hcomm, hinter, by rw [hJM] at htop; exact htop, hnat⟩
    have hperm' : ∀ g ∈ autI hU' M, ∀ L ∈ I, B1.conjAut g L ∈ I := fun g hg L hL =>
      (hperm g hg L hL).1
    have hcov := s3Factor_covered_rel' hX hP hK₃n hU' I hMN hcard hJM hSyl hperm' hfamR
    set KA : Subgroup X := Subgroup.centralizer (T₁ : Set X) ⊓ M with hKA
    set KB : Subgroup X := Subgroup.normalizer (T₂ : Set X) ⊓ M with hKB
    have hcov' : ∀ L ∈ I, L ≤ autI hU' KA ∨ L ≤ autI hU' KB := by
      intro L hL
      obtain ⟨H₀, hHM, hLH, hH⟩ := hcov L hL
      rcases hH with h | h
      · exact Or.inl (hLH.trans (autI_mono hU' (le_inf h hHM)))
      · exact Or.inr (hLH.trans (autI_mono hU' (le_inf h hHM)))
    set Sg : Subgroup (MulAut (IntMod V hU')) := autI hU' (thompsonJ M) with hSg
    set P3 : Subgroup (MulAut (IntMod V hU')) := pCoreOf 3 (⨆ L ∈ I, L) with hP3
    have hSgI : Sg = (⨆ L ∈ I, L : Subgroup (MulAut (IntMod V hU'))) := hJM
    have hSgn : ∀ g ∈ autI hU' M, ∀ φ ∈ Sg, g * φ * g⁻¹ ∈ Sg := autI_thompsonJ_normalized
    have hψM : ∀ (m : X) (hm : m ∈ M), actM hU' hMN ⟨m, hm⟩ ∈ autI hU' M := fun m hm =>
      (mem_autI hU').2 ⟨⟨m, hMN hm⟩, hm, rfl⟩
    have hP3n : ∀ g ∈ autI hU' M, ∀ φ ∈ P3, g * φ * g⁻¹ ∈ P3 := by
      intro g hg φ hφ
      have hgN : g ∈ Subgroup.normalizer ((⨆ L ∈ I, L : Subgroup (MulAut (IntMod V hU'))) :
          Set (MulAut (IntMod V hU'))) := by
        rw [← hSgI]
        exact B6.mem_normalizer_of_forall_mem (fun x hx => hSgn g hg x hx)
          (fun x hx => by simpa using hSgn g⁻¹ ((autI hU' M).inv_mem hg) x hx)
      have := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 3
        (⨆ L ∈ I, L : Subgroup (MulAut (IntMod V hU'))) hgN
      exact (Subgroup.mem_normalizer_iff.mp this φ).mp hφ
    have hnormPre : ∀ L' : Subgroup (MulAut (IntMod V hU')),
        (∀ g ∈ autI hU' M, ∀ φ ∈ L', g * φ * g⁻¹ ∈ L') →
        ∀ m ∈ M, m ∈ Subgroup.normalizer (preAutM hU' hMN L' : Set X) := by
      intro L' hL' m hm
      have hconj : ∀ m ∈ M, ∀ s ∈ preAutM hU' hMN L', m * s * m⁻¹ ∈ preAutM hU' hMN L' := by
        intro m hm s hs
        obtain ⟨hsM, hψs⟩ := (mem_preAutM hU' hMN).1 hs
        have hmsM : m * s * m⁻¹ ∈ M := M.mul_mem (M.mul_mem hm hsM) (M.inv_mem hm)
        refine (mem_preAutM hU' hMN).2 ⟨hmsM, ?_⟩
        have : actM hU' hMN ⟨m * s * m⁻¹, hmsM⟩ = actM hU' hMN ⟨m, hm⟩ * actM hU' hMN ⟨s, hsM⟩ *
            (actM hU' hMN ⟨m, hm⟩)⁻¹ := by
          rw [← map_inv, ← map_mul, ← map_mul]; rfl
        rw [this]
        exact hL' _ (hψM m hm) _ hψs
      exact B6.mem_normalizer_of_forall_mem (hconj m hm)
        (fun s hs => by simpa using hconj m⁻¹ (M.inv_mem hm) s hs)
    have hNQ : ∀ L' : Subgroup (MulAut (IntMod V hU')),
        (∀ g ∈ autI hU' M, ∀ φ ∈ L', g * φ * g⁻¹ ∈ L') →
        A ≤ Subgroup.normalizer ((A ⊓ (preAutM hU' hMN L' ⊔ B) : Subgroup X) : Set X) := by
      intro L' hL' a ha
      have h1 : a ∈ Subgroup.normalizer (preAutM hU' hMN L' : Set X) :=
        hnormPre L' hL' a (hAM ha)
      have h2 : a ∈ Subgroup.normalizer (B : Set X) := mem_normalizer_of_normal'' hB a
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ha,
        Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨h1, h2⟩⟩
    have hkerA : ∀ x ∈ A, ∀ hx : x ∈ M, actM hU' hMN ⟨x, hx⟩ = 1 → x ∈ gnC T := by
      intro x hxA hxM h1
      exact hker ⟨hAK hxA, (actM_eq_one_iff hU' hMN ⟨x, hxM⟩).1 h1⟩
    have hkerB : ∀ z ∈ A, ∀ hz : z ∈ M, actM hU' hMN ⟨z, hz⟩ ∈ autI hU' B → z ∈ B := by
      intro z hzA hzM h
      obtain ⟨g, hgB, hg⟩ := (mem_autI hU').1 h
      have hgA : (g : X) ∈ A := hBA hgB
      have hgM : (g : X) ∈ M := hAM hgA
      have hyA' : (g : X)⁻¹ * z ∈ A := A.mul_mem (A.inv_mem hgA) hzA
      have hyM : (g : X)⁻¹ * z ∈ M := M.mul_mem (M.inv_mem hgM) hzM
      have h1 : actM hU' hMN ⟨(g : X)⁻¹ * z, hyM⟩ = 1 := by
        have : actM hU' hMN ⟨(g : X)⁻¹ * z, hyM⟩ =
            (actM hU' hMN ⟨(g : X), hgM⟩)⁻¹ * actM hU' hMN ⟨z, hzM⟩ := by
          rw [← map_inv, ← map_mul]; rfl
        rw [this]
        have hg' : actM hU' hMN ⟨(g : X), hgM⟩ = actM hU' hMN ⟨z, hzM⟩ := hg
        rw [hg']; group
      have hmem : (g : X)⁻¹ * z ∈ B := hCB (hkerA _ hyA' hyM h1)
      have : z = (g : X) * ((g : X)⁻¹ * z) := by group
      rw [this]
      exact B.mul_mem hgB hmem
    have hAn : ∀ g ∈ autI hU' M, ∀ φ ∈ autI hU' A, g * φ * g⁻¹ ∈ autI hU' A := by
      intro g hg φ hφ
      obtain ⟨m, hmM, rfl⟩ := (mem_autI hU').1 hg
      obtain ⟨a, haA, rfl⟩ := (mem_autI hU').1 hφ
      refine (mem_autI hU').2 ⟨m * a * m⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
      show (m : X) * (a : X) * (m : X)⁻¹ ∈ A
      exact hA.conj_mem _ haA m
    by_cases hR3 : A ⊓ preAutM hU' hMN P3 ≤ B
    ·
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      set Q : Subgroup X := A ⊓ (preAutM hU' hMN Sg ⊔ B) with hQdef
      have hQ2 : ∀ q ∈ Q, ∃ k : ℕ, q ^ 2 ^ k ∈ B := by
        intro q hq
        obtain ⟨s, hs, b', hb', hsb⟩ := Subgroup.mem_sup_of_normal_right.mp hq.2
        have hsA : s ∈ A := by
          have : s = q * b'⁻¹ := by rw [← hsb]; group
          rw [this]
          exact A.mul_mem hq.1 (A.inv_mem (hBA hb'))
        obtain ⟨hsM, hψs⟩ := (mem_preAutM hU' hMN).1 hs
        have hpsisS : actM hU' hMN ⟨s, hsM⟩ ∈
            (⨆ L ∈ I, L : Subgroup (MulAut (IntMod V hU'))) := by
          rw [← hSgI]; exact hψs
        have hsq : (actM hU' hMN ⟨s, hsM⟩) ^ 2 ∈ P3 :=
          hfam.sq_mem_pCore I subset_rfl _ hpsisS
        have hs2M : s ^ 2 ∈ M := M.pow_mem hsM 2
        have hs2 : s ^ 2 ∈ B := by
          apply hR3
          refine ⟨A.pow_mem hsA 2, (mem_preAutM hU' hMN).2 ⟨hs2M, ?_⟩⟩
          have : actM hU' hMN ⟨s ^ 2, hs2M⟩ = (actM hU' hMN ⟨s, hsM⟩) ^ 2 := by
            rw [← map_pow]; rfl
          rw [this]; exact hsq
        refine ⟨1, ?_⟩
        have hq2 : q ^ 2 ^ 1 = s ^ 2 * (s⁻¹ * b' * s * b') := by rw [pow_one, ← hsb, pow_two]; group
        rw [hq2]
        have hc : s⁻¹ * b' * s ∈ B := by simpa using hB.conj_mem b' hb' s⁻¹
        exact B.mul_mem hs2 (B.mul_mem hc hb')
      by_cases hQB : Q ≤ B
      · right; left
        rw [Subgroup.commutator_le]
        intro a ha j hj
        apply hQB
        have haM : a ∈ M := hAM ha
        have hjM : j ∈ M := hTM (B6.thompsonJ_le T hj)
        have hcM : ⁅a, j⁆ ∈ M := by
          rw [commutatorElement_def]
          exact M.mul_mem (M.mul_mem (M.mul_mem haM hjM) (M.inv_mem haM)) (M.inv_mem hjM)
        refine ⟨?_, Subgroup.mem_sup_left ?_⟩
        · have : ⁅a, j⁆ = a * (j * a⁻¹ * j⁻¹) := by rw [commutatorElement_def]; group
          rw [this]
          exact A.mul_mem ha (hA.conj_mem _ (A.inv_mem ha) j)
        · refine (mem_preAutM hU' hMN).2 ⟨hcM, ?_⟩
          have hjJ : j ∈ thompsonJ M := thompsonJ_le_thompsonJ_of_isSylowTwoOf hSylM hj
          have hψj : actM hU' hMN ⟨j, hjM⟩ ∈ Sg := convI_mem_autI hU' hjJ (hMN hjM)
          have : actM hU' hMN ⟨⁅a, j⁆, hcM⟩ = actM hU' hMN ⟨a, haM⟩ * actM hU' hMN ⟨j, hjM⟩ *
              (actM hU' hMN ⟨a, haM⟩)⁻¹ * (actM hU' hMN ⟨j, hjM⟩)⁻¹ := by
            show actM hU' hMN (⁅(⟨a, haM⟩ : ↥M), (⟨j, hjM⟩ : ↥M)⁆) = _
            rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
          rw [this]
          exact Sg.mul_mem (hSgn _ (hψM a haM) _ hψj) (Sg.inv_mem hψj)
      · left
        exact forall_pow_mem_of_chief_of_pSection (r := 2) hA hB hBA hchief inf_le_left
          (hNQ Sg hSgn) hQ2 hQB
    ·
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hp3 : IsPGroup 3 P3 := CFSG.LieType.BorelTits.pCoreOf_isPGroup 3 _
      set R : Subgroup X := A ⊓ (preAutM hU' hMN P3 ⊔ B) with hRdef
      have hR3pow : ∀ x ∈ R, ∃ k : ℕ, x ^ 3 ^ k ∈ B := by
        intro x hx
        obtain ⟨p, hp, b', hb', hpb⟩ := Subgroup.mem_sup_of_normal_right.mp hx.2
        have hpA : p ∈ A := by
          have : p = x * b'⁻¹ := by rw [← hpb]; group
          rw [this]
          exact A.mul_mem hx.1 (A.inv_mem (hBA hb'))
        obtain ⟨hpM, hψp⟩ := (mem_preAutM hU' hMN).1 hp
        obtain ⟨k, hk⟩ := hp3 ⟨_, hψp⟩
        have hk1 : (actM hU' hMN ⟨p, hpM⟩) ^ 3 ^ k = 1 := by
          simpa using congrArg Subtype.val hk
        have hpkM : p ^ 3 ^ k ∈ M := M.pow_mem hpM _
        have hpk1 : actM hU' hMN ⟨p ^ 3 ^ k, hpkM⟩ = 1 := by
          have : actM hU' hMN ⟨p ^ 3 ^ k, hpkM⟩ = (actM hU' hMN ⟨p, hpM⟩) ^ 3 ^ k := by
            rw [← map_pow]; rfl
          rw [this]; exact hk1
        refine ⟨k, ?_⟩
        rw [← hpb]
        exact pow_mul_mem_of_pow_mem hB hb' (hCB (hkerA _ (A.pow_mem hpA _) hpkM hpk1))
      have hRne : ¬ R ≤ B := fun h => hR3 (fun x hx => h ⟨hx.1, Subgroup.mem_sup_left hx.2⟩)
      have h3grp : ∀ a ∈ A, ∃ k : ℕ, a ^ 3 ^ k ∈ B :=
        forall_pow_mem_of_chief_of_pSection (r := 3) hA hB hBA hchief inf_le_left
          (hNQ P3 hP3n) hR3pow hRne
      right; right
      refine ⟨h3grp, ?_⟩
      obtain ⟨x, hxA, hxP, hxB⟩ : ∃ x ∈ A, x ∈ preAutM hU' hMN P3 ∧ x ∉ B := by
        by_contra hcon
        push Not at hcon
        exact hR3 (fun x hx => hcon x hx.1 hx.2)
      obtain ⟨hxM, hψxP⟩ := (mem_preAutM hU' hMN).1 hxP
      set y := actM hU' hMN ⟨x, hxM⟩ with hy
      have hyS : y ∈ (⨆ L ∈ I, L : Subgroup (MulAut (IntMod V hU'))) :=
        CFSG.LieType.BorelTits.pCoreOf_le 3 _ hψxP
      have hy3 : y ^ 3 = 1 := hfam.pow_three_of_mem_pCore hψxP
      have hyA : y ∈ autI hU' A := (mem_autI hU').2 ⟨⟨x, hMN hxM⟩, hxA, rfl⟩
      have hyB : y ∉ autI hU' B := fun h => hxB (hkerB x hxA hxM h)
      obtain ⟨a, haKA, b, hbKB, s, hs, -, -, hyab, ha3, hb3, hsa, hsb⟩ :=
        hfam.exists_dec (KA := autI hU' KA) (KB := autI hU' KB) hcov' I subset_rfl y hyS hy3
      have hsM : s ∈ autI hU' M := autI_mono hU' (B6.thompsonJ_le M) (by rw [← hSg, hSgI]; exact hs)
      have hconjy : s * y * s⁻¹ * y⁻¹ ∈ autI hU' A :=
        (autI hU' A).mul_mem (hAn s hsM y hyA) ((autI hU' A).inv_mem hyA)
      have hcomp : s * y * s⁻¹ * y⁻¹ = (a⁻¹) ^ 2 := by
        rw [hyab]
        calc s * (a * b) * s⁻¹ * (a * b)⁻¹ = (s * a * s⁻¹) * (s * b * s⁻¹) * (a * b)⁻¹ := by group
          _ = a⁻¹ * b * (a * b)⁻¹ := by rw [hsa, hsb]
          _ = (a⁻¹) ^ 2 := by group
      have ha_inv : a⁻¹ ∈ autI hU' A := by
        have h3 : a⁻¹ ^ 3 = 1 := by rw [inv_pow, ha3, inv_one]
        have : a⁻¹ = ((a⁻¹) ^ 2) ^ 2 := by
          calc a⁻¹ = a⁻¹ * a⁻¹ ^ 3 := by rw [h3, mul_one]
            _ = ((a⁻¹) ^ 2) ^ 2 := by group
        rw [this]
        exact (autI hU' A).pow_mem (hcomp ▸ hconjy) 2
      have haA : a ∈ autI hU' A := by simpa using (autI hU' A).inv_mem ha_inv
      have hbA : b ∈ autI hU' A := by
        have : b = a⁻¹ * y := by rw [hyab]; group
        rw [this]
        exact (autI hU' A).mul_mem ha_inv hyA
      have hlift : ∀ KK : Subgroup X, KK ≤ M → ∀ z : MulAut (IntMod V hU'), z ∈ autI hU' KK →
          z ∈ autI hU' A → z ∉ autI hU' B → z ^ 3 = 1 →
          ∃ x ∈ KK, x ∈ A ∧ x ∉ B ∧ ∃ k : ℕ, orderOf x = 3 ^ k := by
        intro KK hKKM z hzKK hzA hzB hz3
        obtain ⟨g, hgKK, hgz⟩ := (mem_autI hU').1 hzKK
        have hgM : (g : X) ∈ M := hKKM hgKK
        obtain ⟨m, hm3, k, hk⟩ := exists_three_part (g : X)
        have hh'KK : (g : X) ^ m ∈ KK := KK.pow_mem hgKK m
        have hh'M : (g : X) ^ m ∈ M := M.pow_mem hgM m
        have hpsi : actM hU' hMN ⟨(g : X) ^ m, hh'M⟩ = z := by
          have : actM hU' hMN ⟨(g : X) ^ m, hh'M⟩ = (actM hU' hMN ⟨(g : X), hgM⟩) ^ m := by
            rw [← map_pow]; rfl
          rw [this]
          have hgz' : actM hU' hMN ⟨(g : X), hgM⟩ = z := hgz
          rw [hgz']
          calc z ^ m = z ^ (3 * (m / 3) + m % 3) := by rw [Nat.div_add_mod]
            _ = z := by rw [pow_add, pow_mul, hz3, one_pow, one_mul, hm3, pow_one]
        have hh'K₃ : (g : X) ^ m ∈ K₃ := by
          refine mem_of_mem_sup_of_pow_mem hK₃n hX.sylow.2.1 hh'M (k := k) ?_
          have : ((g : X) ^ m) ^ 3 ^ k = 1 := by rw [← hk]; exact pow_orderOf_eq_one _
          rw [this]
          exact K₃.one_mem
        obtain ⟨ga, hgaA, hgaz⟩ := (mem_autI hU').1 hzA
        have hgaM : (ga : X) ∈ M := hAM hgaA
        have hc : ((ga : X)⁻¹ * (g : X) ^ m) ∈ gnC T := by
          have hmem : ((ga : X)⁻¹ * (g : X) ^ m) ∈ K₃ :=
            K₃.mul_mem (K₃.inv_mem (hAK hgaA)) hh'K₃
          have hMm : ((ga : X)⁻¹ * (g : X) ^ m) ∈ M := M.mul_mem (M.inv_mem hgaM) hh'M
          have h1 : actM hU' hMN ⟨(ga : X)⁻¹ * (g : X) ^ m, hMm⟩ = 1 := by
            have : actM hU' hMN ⟨(ga : X)⁻¹ * (g : X) ^ m, hMm⟩ =
                (actM hU' hMN ⟨(ga : X), hgaM⟩)⁻¹ * actM hU' hMN ⟨(g : X) ^ m, hh'M⟩ := by
              rw [← map_inv, ← map_mul]; rfl
            rw [this, hpsi]
            have hgaz' : actM hU' hMN ⟨(ga : X), hgaM⟩ = z := hgaz
            rw [hgaz']; group
          exact hker ⟨hmem, (actM_eq_one_iff hU' hMN _).1 h1⟩
        refine ⟨(g : X) ^ m, hh'KK, ?_, ?_, k, hk⟩
        · have : (g : X) ^ m = (ga : X) * ((ga : X)⁻¹ * (g : X) ^ m) := by group
          rw [this]
          exact A.mul_mem hgaA (hBA (hCB hc))
        · intro hB'
          apply hzB
          have hgaB : (ga : X) ∈ B := by
            have : (ga : X) = (g : X) ^ m * ((ga : X)⁻¹ * (g : X) ^ m)⁻¹ := by group
            rw [this]
            exact B.mul_mem hB' (B.inv_mem (hCB hc))
          rw [← hgaz]
          exact convI_mem_autI hU' hgaB (hMN hgaM)
      by_cases hbad : a ∈ autI hU' B
      · have hbB : b ∉ autI hU' B := fun hb =>
          hyB (by rw [hyab]; exact (autI hU' B).mul_mem hbad hb)
        obtain ⟨x', hx'KB, hx'A, hx'B, k, hk⟩ := hlift KB inf_le_right b hbKB hbA hbB hb3
        exact ⟨x', hx'A, hx'B, ⟨k, hk⟩, Or.inr hx'KB.1⟩
      · obtain ⟨x', hx'KA, hx'A, hx'B, k, hk⟩ := hlift KA inf_le_right a haKA haA hbad ha3
        exact ⟨x', hx'A, hx'B, ⟨k, hk⟩, Or.inl hx'KA.1⟩

end Main

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
