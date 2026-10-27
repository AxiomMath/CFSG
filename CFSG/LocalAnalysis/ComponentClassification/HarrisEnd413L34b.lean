module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEnd413L34a
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndOddLayer
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndTools

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

theorem HarrisEnd.card_le_twoPart_of_dvd {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    {n : ℕ} (hn : n ≠ 0) (hdvd : Nat.card P ∣ n) : Nat.card P ≤ 2 ^ n.factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := hP.exists_card_eq
  rw [ha] at hdvd ⊢
  exact Nat.pow_le_pow_right (by norm_num)
    ((Nat.prime_two.pow_dvd_iff_le_factorization hn).mp hdvd)

theorem HarrisEnd.closure_sr_eq_top (n : ℕ) [NeZero n] :
    closure {DihedralGroup.sr (0 : ZMod n), DihedralGroup.sr 1} = ⊤ := by
  rw [eq_top_iff]
  have h1 : DihedralGroup.r (1 : ZMod n) ∈
      closure {DihedralGroup.sr (0 : ZMod n), DihedralGroup.sr 1} := by
    have : DihedralGroup.sr (0 : ZMod n) * DihedralGroup.sr 1 = DihedralGroup.r 1 := by
      rw [DihedralGroup.sr_mul_sr, sub_zero]
    rw [← this]
    exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  have hr : ∀ k : ZMod n, DihedralGroup.r k ∈
      closure {DihedralGroup.sr (0 : ZMod n), DihedralGroup.sr 1} := by
    intro k
    rw [← ZMod.natCast_zmod_val k, ← DihedralGroup.r_one_pow]
    exact pow_mem h1 _
  rintro (k | k) -
  · exact hr k
  · have : DihedralGroup.sr (0 : ZMod n) * DihedralGroup.r k = DihedralGroup.sr k := by
      rw [DihedralGroup.sr_mul_r, zero_add]
    rw [← this]
    exact mul_mem (subset_closure (by simp)) (hr k)

omit [Finite X] in
theorem HarrisEnd.conjOn_of_mem {G : Type} [Group G] {N : Subgroup G} [N.Normal] {g : G}
    (hg : g ∈ N) : conjOn N g = MulAut.conj (⟨g, hg⟩ : ↥N) :=
  MulEquiv.ext fun n => Subtype.ext (by rw [conjOn_apply, MulAut.conj_apply]; rfl)

namespace Setting46e

theorem l34_exists_x (hs : Setting46e t L p f S w z V i j)
    (h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j))
    (hY : Blueprint.LieModel ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) .PSL 3 2 2)
    (hout : conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) (hs.setup.tBar i j) ∉
      innAut ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) :
    ∃ x ∈ S ⊓ L, x ^ 2 = 1 ∧ x ≠ 1 ∧
      ∀ k ∈ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j),
        ∀ (hx : x ∈ centralizer ({t} : Set X)) (hk : k ∈ centralizer ({t} : Set X)),
          hs.standing.rho ⟨x, hx⟩ ≠ hs.standing.rho ⟨k, hk⟩ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, ⟨e⟩⟩ := hs.l34_structure h412 hY hout
  set h := hs.standing with hh
  set H := centralizer ({t} : Set X) with hH
  set K := centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j) with hK
  have hKH : K ≤ H := centralizerResidual_le_left.trans h.config.le_centralizer
  have hDH : S ⊓ L ≤ H := inf_le_left.trans hs.sylow.le
  have hK3 : (Nat.card K).factorization 2 = 3 := by
    have hD := hs.lemma45.isSylowOf_Dstar.card_eq
    have hidx := relIndex_mul_card (inf_le_left : S ⊓ L ⊓ K ≤ S ⊓ L)
    rw [hs.lemma45.relIndex_Dstar, Nat.card_congr e.toEquiv, DihedralGroup.nat_card, hD] at hidx
    have h2 : 2 ^ (Nat.card K).factorization 2 = 2 ^ 3 :=
      Nat.eq_of_mul_eq_mul_left (by norm_num) hidx
    exact Nat.pow_right_injective le_rfl h2
  set ρK := (h.rho.comp (inclusion hKH)).range with hρK
  set ρD := (h.rho.comp (inclusion hDH)).range with hρD
  have hρKle : ∀ P : Subgroup (MulAut (Bar L)), P ≤ ρK → IsPGroup 2 P → Nat.card P ≤ 8 := by
    intro P hP hP2
    have hdvd : Nat.card P ∣ Nat.card K :=
      (Subgroup.card_dvd_of_le hP).trans (Subgroup.card_range_dvd _)
    have := HarrisEnd.card_le_twoPart_of_dvd hP2 Nat.card_pos.ne' hdvd
    rwa [hK3] at this
  have hinj : Function.Injective (h.rho.comp (inclusion hDH)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro d hd
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hd
    have h1 := h.mem_zpowers_of_rho_eq_one hs.sylow d.2.1 hd
    exact (mem_bot).mpr (Subtype.ext (h.eq_one_of_mem_zpowers_of_mem h1 d.2.2))
  have hρD16 : Nat.card ρD = 16 := by
    rw [hρD, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_congr e.toEquiv,
      DihedralGroup.nat_card]
    norm_num
  have hρD2 : IsPGroup 2 ρD := by
    refine IsPGroup.of_card (n := 4) ?_
    rw [hρD16]
    norm_num
  have hgen : ¬ (h.rho.comp (inclusion hDH) (e.symm (DihedralGroup.sr 0)) ∈ ρK ∧
      h.rho.comp (inclusion hDH) (e.symm (DihedralGroup.sr 1)) ∈ ρK) := by
    rintro ⟨h0, h1⟩
    have hle : ρD ≤ ρK := by
      rintro _ ⟨d, rfl⟩
      have hd : d ∈ ((closure {DihedralGroup.sr (0 : ZMod (2 ^ 3)), DihedralGroup.sr 1}).map
          e.symm.toMonoidHom) := by
        rw [HarrisEnd.closure_sr_eq_top]
        exact ⟨e d, mem_top _, by simp⟩
      rw [MonoidHom.map_closure] at hd
      have hcl : closure ((e.symm.toMonoidHom) '' {DihedralGroup.sr (0 : ZMod (2 ^ 3)),
          DihedralGroup.sr 1}) ≤ ρK.comap (h.rho.comp (inclusion hDH)) := by
        rw [closure_le]
        rintro _ ⟨g, hg, rfl⟩
        rcases hg with rfl | rfl
        · exact h0
        · exact h1
      exact hcl hd
    have := hρKle ρD hle hρD2
    omega
  have hsr : ∀ k : ZMod (2 ^ 3), (e.symm (DihedralGroup.sr k) : X) ^ 2 = 1 ∧
      (e.symm (DihedralGroup.sr k) : X) ≠ 1 := by
    intro k
    constructor
    · rw [← Subgroup.coe_pow, ← map_pow, sq, DihedralGroup.sr_mul_self, map_one,
        Subgroup.coe_one]
    · intro h1
      have h2 : e.symm (DihedralGroup.sr k) = 1 := Subtype.ext h1
      rw [← map_one e.symm] at h2
      have h3 := e.symm.injective h2
      rw [DihedralGroup.one_def] at h3
      cases h3
  have hnot : ∀ k : ZMod (2 ^ 3),
      h.rho.comp (inclusion hDH) (e.symm (DihedralGroup.sr k)) ∉ ρK →
      ∀ c ∈ K, ∀ (hx : (e.symm (DihedralGroup.sr k) : X) ∈ H) (hc : c ∈ H),
        h.rho ⟨_, hx⟩ ≠ h.rho ⟨c, hc⟩ := by
    intro k hk c hcK hx hc heq
    apply hk
    refine ⟨⟨c, hcK⟩, ?_⟩
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
    exact heq.symm
  by_cases h0 : h.rho.comp (inclusion hDH) (e.symm (DihedralGroup.sr 0)) ∈ ρK
  · have h1 : h.rho.comp (inclusion hDH) (e.symm (DihedralGroup.sr 1)) ∉ ρK :=
      fun h1 => hgen ⟨h0, h1⟩
    exact ⟨_, (e.symm (DihedralGroup.sr 1)).2, (hsr 1).1, (hsr 1).2, hnot 1 h1⟩
  · exact ⟨_, (e.symm (DihedralGroup.sr 0)).2, (hsr 0).1, (hsr 0).2, hnot 0 h0⟩

theorem rho_eq_one_of_mem_oddCore_M (hs : Setting46e t L p f S w z V i j) {o : X}
    (ho : o ∈ (pPrimeCore 2 ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))).map
      (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)).subtype)
    (hoH : o ∈ centralizer ({t} : Set X)) : hs.standing.rho ⟨o, hoH⟩ = 1 := by
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  set M := centralizer ({β} : Set X) with hM
  set A := centralizer ({t} : Set X) ⊓ centralizer {β} with hA
  set N := (pPrimeCore 2 ↥M).map M.subtype ⊓ A with hN
  have hoM : o ∈ M := map_subtype_le _ ho
  have hoN : o ∈ N := Subgroup.mem_inf.mpr ⟨ho, Subgroup.mem_inf.mpr ⟨hoH, hoM⟩⟩
  have hNA : N ≤ (pPrimeCore 2 ↥A).map A.subtype := by
    refine le_map_pPrimeCore inf_le_right (fun a ha n hn => Subgroup.mem_inf.mpr ⟨?_, ?_⟩) ?_
    · exact conj_mem_map_pPrimeCore_self (Subgroup.mem_inf.mp ha).2 (Subgroup.mem_inf.mp hn).1
    · exact mul_mem (mul_mem ha (Subgroup.mem_inf.mp hn).2) (inv_mem ha)
    · exact (coprime_card_map_pPrimeCore M).coprime_dvd_right
        (Subgroup.card_dvd_of_le inf_le_left)
  have h1 := hNA hoN
  rw [hs.lemma45.oddCore_M] at h1
  have h2 : o ∈ centralizer ({t} : Set X) ⊓ coreActionKernel L := by
    rw [hs.standing.dihedral.kernel_eq]
    exact mem_sup_left h1.2
  exact (hs.standing.mem_ker_rho ⟨o, hoH⟩).mpr h2.2

theorem l34_x_outer (hs : Setting46e t L p f S w z V i j)
    [IsSimpleGroup ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))]
    (h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j))
    (hY : Blueprint.LieModel ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) .PSL 3 2 2)
    (hout : conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) (hs.setup.tBar i j) ∉
      innAut ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))))
    {x : X} (hxD : x ∈ S ⊓ L)
    (hxρ : ∀ k ∈ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j),
        ∀ (hx : x ∈ centralizer ({t} : Set X)) (hk : k ∈ centralizer ({t} : Set X)),
          hs.standing.rho ⟨x, hx⟩ ≠ hs.standing.rho ⟨k, hk⟩)
    {g : X} (hg : g = x ∨ g = x * t)
    (hgM : g ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) :
    conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) (QuotientGroup.mk ⟨g, hgM⟩) ∉
      innAut ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := by
  intro hin
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  set M := centralizer ({β} : Set X) with hM
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hπ
  set h := hs.standing with hh
  set H := centralizer ({t} : Set X) with hH
  have htH : t ∈ H := mem_centralizer_singleton_iff.mpr rfl
  have hxH : x ∈ H := h.config.le_centralizer hxD.2
  have hgH : g ∈ H := by
    rcases hg with rfl | rfl
    · exact hxH
    · exact mul_mem hxH htH
  have htM := hs.setup.t_mem_centralizer_beta i j
  have hgC : π ⟨g, hgM⟩ ∈ centralizer {hs.setup.tBar i j} := by
    rw [mem_centralizer_singleton_iff]
    have hgt : (⟨g, hgM⟩ : ↥M) * ⟨t, htM⟩ = ⟨t, htM⟩ * ⟨g, hgM⟩ :=
      Subtype.ext (mem_centralizer_singleton_iff.mp hgH)
    change π ⟨g, hgM⟩ * π ⟨t, htM⟩ = π ⟨t, htM⟩ * π ⟨g, hgM⟩
    rw [← map_mul, ← map_mul, hgt]
  obtain ⟨c, hc, n, hn, hgcn⟩ := exists_mul_of_conjOn_mem_innAut hs.KBar_le_layer
    (nonabelian_of_lieModel_psl2 (hs.lieModel_KBar h412)) hgC hin
  rw [hs.centralizer_layer_inf_centralizer_tBar h412] at hc
  obtain ⟨b, rfl⟩ := mem_zpowers_iff.mp hc
  rw [(hs.l34_structure h412 hY hout).1] at hn
  obtain ⟨k', hk', rfl⟩ := hn
  have hkK : (k' : X) ∈ centralizerResidual L β := hk'
  have hkH : (k' : X) ∈ H := (centralizerResidual_le_left.trans h.config.le_centralizer) hkK
  set β' : ↥M := ⟨β, mem_centralizer_singleton_iff.mpr rfl⟩ with hβ'
  set o : ↥M := (β' ^ b * k')⁻¹ * ⟨g, hgM⟩ with ho
  have hoO : o ∈ pPrimeCore 2 ↥M := by
    have h1 : π o = 1 := by
      rw [ho, map_mul, map_inv, map_mul, map_zpow]
      change (betaBar β ^ b * π k')⁻¹ * π ⟨g, hgM⟩ = 1
      rw [hgcn, inv_mul_cancel]
    rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have hβH : β ∈ H := hs.setup.beta_mem_H i j
  have hoH : (o : X) ∈ H := by
    rw [ho, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul, Subgroup.coe_zpow]
    exact mul_mem (inv_mem (mul_mem (zpow_mem hβH b) hkH)) hgH
  have hρo : h.rho ⟨(o : X), hoH⟩ = 1 := hs.rho_eq_one_of_mem_oddCore_M ⟨o, hoO, rfl⟩ hoH
  have hoX : (o : X) = (β ^ b * (k' : X))⁻¹ * g := by
    rw [ho, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul, Subgroup.coe_zpow]
  have hgeq : (⟨g, hgH⟩ : ↥H) = ⟨β, hβH⟩ ^ b * ⟨k', hkH⟩ * ⟨o, hoH⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_zpow]
    rw [hoX]
    group
  have hρg : h.rho ⟨g, hgH⟩ = h.rho ⟨x, hxH⟩ := by
    rcases hg with rfl | rfl
    · rfl
    · rw [show (⟨x * t, hgH⟩ : ↥H) = ⟨x, hxH⟩ * ⟨t, htH⟩ from rfl, map_mul, h.rho_t, mul_one]
  rw [hgeq, map_mul, map_mul, map_zpow, hρo, mul_one] at hρg
  have hxInn : h.rho ⟨x, hxH⟩ ∈ innAut (Bar L) :=
    ⟨QuotientGroup.mk ⟨x, hxD.2⟩, (h.rho_of_mem ⟨x, hxD.2⟩).symm⟩
  have hkInn : h.rho ⟨k', hkH⟩ ∈ innAut (Bar L) :=
    ⟨QuotientGroup.mk ⟨k', centralizerResidual_le_left hkK⟩,
      (h.rho_of_mem ⟨k', centralizerResidual_le_left hkK⟩).symm⟩
  have hβInn : h.rho ⟨β, hβH⟩ ^ b ∈ innAut (Bar L) := by
    have := mul_mem hxInn (inv_mem hkInn)
    rwa [← hρg, mul_inv_cancel_right] at this
  have hβ2 : h.rho ⟨β, hβH⟩ ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨β, hβH⟩ : ↥H) ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, hs.setup.sq_eq_one_of_mem_X (beta_mem_X i j), Subgroup.coe_one])
    rw [this, map_one]
  rcases Int.even_or_odd' b with ⟨c, rfl | rfl⟩
  · rw [zpow_mul, zpow_ofNat, hβ2, one_zpow, one_mul] at hρg
    exact hxρ k' hkK hxH hkH hρg.symm
  · rw [zpow_add, zpow_mul, zpow_ofNat, hβ2, one_zpow, one_mul, zpow_one] at hβInn
    exact hs.setup.rho_beta_not_mem_inn i j hβInn

theorem l34_conj_tx (hKF : AutPSL2FusionInput) (hs : Setting46e t L p f S w z V i j)
    [IsSimpleGroup ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))]
    (h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j))
    (hY : Blueprint.LieModel ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) .PSL 3 2 2)
    (hout : conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) (hs.setup.tBar i j) ∉
      innAut ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))))
    {x : X} (hxD : x ∈ S ⊓ L) (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) :
    ∃ c : X, c * t * c⁻¹ = x * t := by
  obtain ⟨-, hcos, -, -⟩ := l34_outer_facts hY (hs.orderOf_conjOn_tBar h412) hout
    hs.p_ne_two hs.sixteen_dvd (hs.lieModel_layerIn_fixedPoints h412)
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  set M := centralizer ({β} : Set X) with hM
  set E := layer (MBar β) with hE
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hπ
  set h := hs.standing with hh
  have hzK : z ∈ centralizerResidual L β := hs.lemma45.z_mem.2
  have hzM : z ∈ M := K_le_centralizer_beta i j hzK
  have htM := hs.setup.t_mem_centralizer_beta i j
  have hzt : z * t = t * z := mem_centralizer_singleton_iff.mp
    (h.config.le_centralizer hs.setup.z_mem.2)
  have ht2 : t ^ 2 = 1 := by rw [← h.config.orderOf_eq]; exact pow_orderOf_eq_one t
  have hz2 : z ^ 2 = 1 := by rw [← hs.setup.z_order]; exact pow_orderOf_eq_one z
  have hzt2 : (z * t) ^ 2 = 1 := by
    rw [(show Commute z t from hzt).mul_pow, hz2, ht2, one_mul]
  set zb := π ⟨z, hzM⟩ with hzb
  have hzE : zb ∈ E := hs.KBar_le_layer ⟨⟨z, hzM⟩, hzK, rfl⟩
  have htb : hs.setup.tBar i j = π ⟨t, htM⟩ := rfl
  have hzτ : MulAut.conj (⟨zb, hzE⟩ : ↥E) * conjOn E (hs.setup.tBar i j) =
      conjOn E (zb * hs.setup.tBar i j) := by
    rw [map_mul, HarrisEnd.conjOn_of_mem hzE]
  have hzτ2 : (MulAut.conj (⟨zb, hzE⟩ : ↥E) * conjOn E (hs.setup.tBar i j)) ^ 2 = 1 := by
    rw [hzτ, ← map_pow, htb, hzb, ← map_mul, ← map_pow]
    have : (⟨z, hzM⟩ * ⟨t, htM⟩ : ↥M) ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_mul, hzt2, Subgroup.coe_one])
    rw [this, map_one, map_one]
  obtain ⟨g, hg⟩ := hcos ⟨zb, hzE⟩ hzτ2
  have hKnab := nonabelian_of_lieModel_psl2 (hs.lieModel_KBar h412)
  have hEC := centralizer_inf_layer_eq_bot hs.KBar_le_layer hKnab
  have hconj : (g : MBar β) * hs.setup.tBar i j * (g : MBar β)⁻¹ =
      zb * hs.setup.tBar i j := by
    have h1 : conjOn E ((g : MBar β) * hs.setup.tBar i j * (g : MBar β)⁻¹) =
        conjOn E (zb * hs.setup.tBar i j) := by
      rw [← hzτ, ← hg, map_mul, map_mul, map_inv, HarrisEnd.conjOn_of_mem g.2]
    have h2 : (g : MBar β) * hs.setup.tBar i j * (g : MBar β)⁻¹ * (zb * hs.setup.tBar i j)⁻¹ ∈
        centralizer (E : Set (MBar β)) ⊓ E := by
      refine mem_inf.mpr ⟨conjOn_eq_one_iff.mp (by rw [map_mul, map_inv, h1, mul_inv_cancel]), ?_⟩
      have hg' : hs.setup.tBar i j * (g : MBar β)⁻¹ * (hs.setup.tBar i j)⁻¹ ∈ E :=
        (inferInstance : E.Normal).conj_mem _ (inv_mem g.2) _
      rw [show (g : MBar β) * hs.setup.tBar i j * (g : MBar β)⁻¹ * (zb * hs.setup.tBar i j)⁻¹ =
        (g : MBar β) * (hs.setup.tBar i j * (g : MBar β)⁻¹ * (hs.setup.tBar i j)⁻¹) * zb⁻¹ by
          group]
      exact mul_mem (mul_mem g.2 hg') (inv_mem hzE)
    rw [hEC, mem_bot, mul_inv_eq_one] at h2
    exact h2
  obtain ⟨g', hg'⟩ := QuotientGroup.mk_surjective (g : MBar β)
  set N := (pPrimeCore 2 ↥M).map M.subtype with hN
  have hNodd : Odd (Nat.card N) := Nat.coprime_two_left.mp (coprime_card_map_pPrimeCore M)
  have hcoset : ((g' : X) * t * (g' : X)⁻¹)⁻¹ * (z * t) ∈ N := by
    have h1 : π ((g' * ⟨t, htM⟩ * g'⁻¹)⁻¹ * (⟨z, hzM⟩ * ⟨t, htM⟩)) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, map_inv, map_mul]
      change ((g' : MBar β) * hs.setup.tBar i j * (g' : MBar β)⁻¹)⁻¹ *
        (zb * hs.setup.tBar i j) = 1
      rw [hg', hconj, inv_mul_cancel]
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact ⟨_, h1, rfl⟩
  have hx₀2 : ((g' : X) * t * (g' : X)⁻¹) ^ 2 = 1 := by
    rw [sq, show (g' : X) * t * (g' : X)⁻¹ * ((g' : X) * t * (g' : X)⁻¹) =
      (g' : X) * (t * t) * (g' : X)⁻¹ by group, ← sq t, ht2, mul_one, mul_inv_cancel]
  obtain ⟨n₀, -, hn₀⟩ := exists_conj_of_mem_coset_odd hNodd hx₀2 hzt2 hcoset
  obtain ⟨g₁, hg₁H, hg₁⟩ := hs.setup.exists_conj_eq_z hKF hxD hx2 hx1
  refine ⟨g₁⁻¹ * (n₀ * g'), ?_⟩
  have hg₁t : g₁⁻¹ * t * g₁ = t := by
    rw [mul_assoc, ← mem_centralizer_singleton_iff.mp hg₁H]
    group
  have hg₁x : g₁⁻¹ * z * g₁ = x := by rw [← hg₁]; group
  calc g₁⁻¹ * (n₀ * g') * t * (g₁⁻¹ * (n₀ * g'))⁻¹
      = g₁⁻¹ * (n₀ * ((g' : X) * t * (g' : X)⁻¹) * n₀⁻¹) * g₁ := by group
    _ = g₁⁻¹ * (z * t) * g₁ := by rw [hn₀]
    _ = (g₁⁻¹ * z * g₁) * (g₁⁻¹ * t * g₁) := by group
    _ = x * t := by rw [hg₁x, hg₁t]

theorem l34_quaternion (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hI : AutPSL2InvolutionInput) (hKF : AutPSL2FusionInput)
    (hs : Setting46e t L p f S w z V i j)
    [IsSimpleGroup ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))]
    (h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j))
    (hY : Blueprint.LieModel ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) .PSL 3 2 2)
    (hout : conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) (hs.setup.tBar i j) ∉
      innAut ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))))
    {x : X} (hxD : x ∈ S ⊓ L) (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1)
    (hxρ : ∀ k ∈ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j),
        ∀ (hx : x ∈ centralizer ({t} : Set X)) (hk : k ∈ centralizer ({t} : Set X)),
          hs.standing.rho ⟨x, hx⟩ ≠ hs.standing.rho ⟨k, hk⟩)
    (hxtM : x * t ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) :
    ∀ P : Sylow 2 ↥(fixedPoints (conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
      (QuotientGroup.mk ⟨x * t, hxtM⟩))), Nonempty (QuaternionGroup 2 ≃* ↥P) := by
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  set M := centralizer ({β} : Set X) with hM
  set E := layer (MBar β) with hE
  obtain ⟨-, -, -, hdich⟩ := l34_outer_facts hY (hs.orderOf_conjOn_tBar h412) hout
    hs.p_ne_two hs.sixteen_dvd (hs.lieModel_layerIn_fixedPoints h412)
  have hxM : x ∈ M := hs.setup.D_le_centralizer_beta i j hxD
  have htM := hs.setup.t_mem_centralizer_beta i j
  have hxt : x * t = t * x := mem_centralizer_singleton_iff.mp
    (hs.standing.config.le_centralizer hxD.2)
  have ht2 : t ^ 2 = 1 := by rw [← hs.standing.config.orderOf_eq]; exact pow_orderOf_eq_one t
  have hxt2 : (x * t) ^ 2 = 1 := by
    rw [(show Commute x t from hxt).mul_pow, hx2, ht2, one_mul]
  have hπxt : (QuotientGroup.mk ⟨x, hxM⟩ : MBar β) * hs.setup.tBar i j =
      QuotientGroup.mk ⟨x * t, hxtM⟩ := rfl
  have hστ : conjOn E (QuotientGroup.mk ⟨x, hxM⟩) * conjOn E (hs.setup.tBar i j) =
      conjOn E (QuotientGroup.mk ⟨x * t, hxtM⟩) := by
    rw [← map_mul, hπxt]
  have hσ2 : conjOn E (QuotientGroup.mk ⟨x, hxM⟩ : MBar β) ^ 2 = 1 := by
    rw [← map_pow, ← QuotientGroup.mk_pow]
    have : (⟨x, hxM⟩ : ↥M) ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, hx2, Subgroup.coe_one])
    rw [this, QuotientGroup.mk_one, map_one]
  have hcomm : conjOn E (QuotientGroup.mk ⟨x, hxM⟩ : MBar β) * conjOn E (hs.setup.tBar i j) =
      conjOn E (hs.setup.tBar i j) * conjOn E (QuotientGroup.mk ⟨x, hxM⟩ : MBar β) := by
    rw [← map_mul, ← map_mul]
    congr 1
    change (QuotientGroup.mk (⟨x, hxM⟩ * ⟨t, htM⟩) : MBar β) =
      QuotientGroup.mk (⟨t, htM⟩ * ⟨x, hxM⟩)
    congr 1
    exact Subtype.ext hxt
  have hσout := hs.l34_x_outer h412 hY hout hxD hxρ (Or.inl rfl) hxM
  have hστout := hs.l34_x_outer h412 hY hout hxD hxρ (Or.inr rfl) hxtM
  rw [← hστ] at hστout
  rcases hdich _ hσ2 hcomm hσout hστout with ⟨-, hQ⟩ | ⟨⟨hsimp, hnab, h60⟩, -⟩
  · rw [hστ] at hQ
    exact hQ
  · exfalso
    rw [hστ] at hsimp hnab h60
    obtain ⟨c, hc⟩ := hs.l34_conj_tx hKF h412 hY hout hxD hx2 hx1
    obtain ⟨-, -, hp7, hf1, -⟩ := hs.l34_structure h412 hY hout
    have hβ2 : β ^ 2 = 1 := hs.setup.sq_eq_one_of_mem_X (beta_mem_X i j)
    have hβC : β ∈ centralizer ({c * t * c⁻¹} : Set X) := by
      rw [hc, mem_centralizer_singleton_iff]
      have h1 : x * β = β * x := mem_centralizer_singleton_iff.mp hxM
      have h2 : t * β = β * t := mem_centralizer_singleton_iff.mp htM
      calc β * (x * t) = (β * x) * t := by group
        _ = (x * β) * t := by rw [h1]
        _ = x * (β * t) := by group
        _ = x * (t * β) := by rw [h2]
        _ = x * t * β := by group
    have hβne : β ≠ c * t * c⁻¹ := by
      rw [hc]
      intro h
      have hmem : β ∈ zpowers t ⊔ (S ⊓ L) := by
        rw [h]
        exact mul_mem (mem_sup_right hxD) (mem_sup_left (mem_zpowers t))
      exact hs.beta.not_mem hmem
    have h44 := hs.lemma44_conj hFC hKC hI hKF c hβC hβ2 hs.beta.ne_one hβne
    rw [hc, hp7, hf1] at h44
    set A := E ⊓ centralizer {(QuotientGroup.mk ⟨x * t, hxtM⟩ : MBar β)} with hA
    have hmap := map_fixedPoints_conjOn (N := E) (QuotientGroup.mk ⟨x * t, hxtM⟩ : MBar β)
    have eA : ↥(fixedPoints (conjOn E (QuotientGroup.mk ⟨x * t, hxtM⟩ : MBar β))) ≃* ↥A :=
      ((fixedPoints (conjOn E (QuotientGroup.mk ⟨x * t, hxtM⟩ : MBar β))).equivMapOfInjective
        E.subtype E.subtype_injective).trans (MulEquiv.subgroupCongr hmap)
    have : IsSimpleGroup ↥A := eA.symm.isSimpleGroup
    have hnabA : ∃ a b : ↥A, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hnab
      exact ⟨eA a, eA b, fun h => hab (eA.injective (by rw [map_mul, map_mul, h]))⟩
    have hA60 : Nat.card ↥A = 60 := by rw [← Nat.card_congr eA.toEquiv, h60]
    refine HarrisEnd.false_of_simple_sixty hxtM hxt2 h44 (A := A) inf_le_right ?_ hnabA hA60
    intro g hg a ha
    refine mem_inf.mpr ⟨(inferInstance : E.Normal).conj_mem a (mem_inf.mp ha).1 g, ?_⟩
    exact mul_mem (mul_mem hg (mem_inf.mp ha).2) (inv_mem hg)

end Setting46e

end CFSG.ComponentClassification.HarrisLit
