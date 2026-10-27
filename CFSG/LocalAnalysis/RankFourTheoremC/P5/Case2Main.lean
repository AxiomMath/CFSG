module

public import CFSG.LocalAnalysis.RankFourTheoremC.P5.Case2Y
public import CFSG.LocalAnalysis.RankFourTheoremC.P5.Case2Borel
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointCase2
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Quot
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
import CFSG.LocalAnalysis.RankFourTheoremC.Equivalence
public import CFSG.LocalAnalysis.RankFourTheoremC.P5.Ctx
public import CFSG.LocalAnalysis.RankFourTheoremC.P5.QK

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.P5

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.LocalAnalysis.RankFourTheoremC Subgroup
open CFSG.ABGLocalTools CFSG.LocalAnalysis.RankThreeTheoremC

variable {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime] {P : Sylow p G}
  {M : Subgroup G} {x : G}

theorem isMulCommutative_of_isPGroup_p {P : Sylow p G} (hPab : IsMulCommutative (P : Subgroup G))
    {Q : Subgroup G} (hQ : IsPGroup p Q) : IsMulCommutative Q := by
  obtain ⟨P', hP'⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P P'
  have h : ((g • P : Sylow p G) : Subgroup G) = (P' : Subgroup G) := by rw [hg]
  rw [Sylow.coe_subgroup_smul] at h
  have hcomm : ∀ a b : G, a ∈ (P' : Subgroup G) → b ∈ (P' : Subgroup G) → a * b = b * a := by
    intro a b ha hb
    rw [← h, Subgroup.mem_smul_pointwise_iff_exists] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    have hab : a' * b' = b' * a' :=
      congrArg Subtype.val ((IsMulCommutative.is_comm (M := (P : Subgroup G))).comm ⟨a', ha'⟩
        ⟨b', hb'⟩)
    show g * a' * g⁻¹ * (g * b' * g⁻¹) = g * b' * g⁻¹ * (g * a' * g⁻¹)
    calc g * a' * g⁻¹ * (g * b' * g⁻¹) = g * (a' * b') * g⁻¹ := by group
      _ = g * (b' * a') * g⁻¹ := by rw [hab]
      _ = g * b' * g⁻¹ * (g * a' * g⁻¹) := by group
  exact IsMulCommutative.of_comm fun a b => Subtype.ext (hcomm a b (hP' a.2) (hP' b.2))

theorem mem_glbPrimeCore_of_mk_eq_one_p {H : Subgroup G} {r : G} (hr : r ∈ H)
    (h : QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨r, hr⟩ = 1) :
    r ∈ GLBPrimeCore p H := by
  have h1 : (⟨r, hr⟩ : H) ∈ primeComplementCore (G := H) p := (QuotientGroup.eq_one_iff _).mp h
  rw [← glbPrimeCore_subgroupOf] at h1
  exact Subgroup.mem_subgroupOf.mp h1

theorem weakClosed_sylow_p {P : Sylow p G} {x : G}
    (hwc : ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x)
    (Q : Sylow p G) (hxQ : x ∈ (Q : Subgroup G)) (g : G)
    (hg : (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (Q : Subgroup G)) :
    (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x := by
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G P Q
  have h : ((c • P : Sylow p G) : Subgroup G) = (Q : Subgroup G) := by rw [hc]
  rw [Sylow.coe_subgroup_smul] at h
  have hmem : ∀ y ∈ (Q : Subgroup G), c⁻¹ * y * c ∈ (P : Subgroup G) := by
    intro y hy
    rw [← h, Subgroup.mem_smul_pointwise_iff_exists] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have : c⁻¹ * (c * z * c⁻¹) * c = z := by group
    show c⁻¹ * (c * z * c⁻¹) * c ∈ (P : Subgroup G)
    rw [this]
    exact hz
  have h1 : (zpowers x).map (MulAut.conj (c⁻¹ * g)).toMonoidHom ≤ (P : Subgroup G) := by
    rintro _ ⟨z, hz, rfl⟩
    have hgz : g * z * g⁻¹ ∈ (Q : Subgroup G) := hg ⟨z, hz, rfl⟩
    have := hmem _ hgz
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev, inv_inv]
    simpa [mul_assoc] using this
  have h2 : (zpowers x).map (MulAut.conj c⁻¹).toMonoidHom ≤ (P : Subgroup G) := by
    rintro _ ⟨z, hz, rfl⟩
    have hz' : z ∈ (Q : Subgroup G) := zpowers_le.mpr hxQ hz
    have := hmem _ hz'
    simpa [MulAut.conj_apply] using this
  have e1 := hwc _ h1
  have e2 := hwc _ h2
  have e3 : (zpowers x).map (MulAut.conj (c⁻¹ * g)).toMonoidHom =
      ((zpowers x).map (MulAut.conj g).toMonoidHom).map (MulAut.conj c⁻¹).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext y
    simp
  apply Subgroup.map_injective (f := (MulAut.conj c⁻¹).toMonoidHom) (MulAut.conj c⁻¹).injective
  rw [← e3, e1, e2]

theorem two_ne_zero_galois_p {n : ℕ} (h5 : 5 ≤ p) : (2 : GaloisField p n) ≠ 0 := by
  intro h0
  have h1 : ((2 : ℕ) : GaloisField p n) = 0 := by exact_mod_cast h0
  have h2 := (CharP.cast_eq_zero_iff (GaloisField p n) p 2).mp h1
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem case2HypP_quotient (hp2 : p ≠ 2) (hS : D1Global G)
    (hPab : IsMulCommutative (P : Subgroup G)) (hMtop : M ≠ ⊤) (hxM : x ∈ M)
    (hxo : orderOf x = p)
    (hwc : ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x) :
    Case2HypP p (M ⧸ primeComplementCore (G := M) p)
      (QuotientGroup.mk' (primeComplementCore (G := M) p) ⟨x, hxM⟩) := by
  have hpp : Nat.Prime p := Fact.out
  set O : Subgroup M := primeComplementCore (G := M) p with hO
  have hxo' : orderOf (⟨x, hxM⟩ : M) = p := by
    rw [Subgroup.orderOf_mk]
    exact hxo
  have hxo'' : orderOf (QuotientGroup.mk' O ⟨x, hxM⟩) = p :=
    orderOf_mk_of_coprime hpp O (primeComplementCore_coprime p) hxo'
  have hab : ∀ S : Sylow p (M ⧸ O), IsMulCommutative (S : Subgroup (M ⧸ O)) :=
    isMulCommutative_sylow_quotient (N := M) fun _ hQ => isMulCommutative_of_isPGroup_p hPab hQ
  exact
    { ne_two := hp2
      core_eq_bot := primeComplementCore_quotient_eq_bot p
      catalog := (catalogSimpleSections_of_isKProper hS.kProper M hMtop).quotient O
      abelian := hab
      ne_one := fun h => by
        rw [h, orderOf_one] at hxo''
        have := hpp.two_le
        omega
      pow_eq_one := by simpa only [hxo''] using pow_orderOf_eq_one (QuotientGroup.mk' O ⟨x, hxM⟩)
      weakClosed := fun Q hxQ g hg => weaklyClosed_map_mk hxo' hab
        (fun Q' hxQ' g' hg' => weakClosed_sylow_p hwc Q' hxQ' g' hg') Q hxQ g hg }

theorem conj_mem_sup_p (hK : P5KFacts) (hG : P5Global G) (hloc : D1Local p P M)
    (h : CFSG.LocalAnalysis.RankFourTheoremC.IsPPoint p P M x) {n : ℕ}
    {f : GaloisField p n → G} {W : Subgroup G} (hB : BorelDataP p P M x f W)
    (hS : PtShape p P x) :
    ∀ m ∈ M, ∀ q ∈ hB.QK, m * q * m⁻¹ ∈ (P : Subgroup G) ⊔ GLBPrimeCore p M := by
  have hpp : Nat.Prime p := Fact.out
  have hPab : IsMulCommutative (P : Subgroup G) := hS.abelian
  have hwc := hS.weak
  have hPM : (P : Subgroup G) ≤ M := sylow_le_of_core hloc
  have hQKM : hB.QK ≤ M := hB.QK_le_P.trans hPM
  have hxM : x ∈ M := hPM hB.x_mem
  have hxo : orderOf x = p := h.elem.2.1
  have hMtop : M ≠ ⊤ := by
    have := hG.glob.simple
    exact CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top hG.glob.nonab hloc.maxLocal.1
  have hp2 : p ≠ 2 := by
    have := hB.five_le
    omega
  have hxo' : orderOf (⟨x, hxM⟩ : M) = p := by
    rw [Subgroup.orderOf_mk]
    exact hxo
  have hbase := case2HypP_quotient hp2 hG.glob hPab hMtop hxM hxo hwc
  set O : Subgroup M := primeComplementCore (G := M) p
  set π : M →* M ⧸ O := QuotientGroup.mk' O
  set xb : M ⧸ O := π ⟨x, hxM⟩ with hxb
  have hfM : ∀ t, f t ∈ M := fun t => hQKM (hB.f_mem_QK t)
  set ρ : GaloisField p n → M ⧸ O := fun t => π ⟨f t, hfM t⟩ with hρ
  set Z : Subgroup (M ⧸ O) := (hB.QK.subgroupOf M).map π with hZ
  have hZmem : ∀ z, z ∈ Z ↔ ∃ t, ρ t = z := by
    intro z
    constructor
    · rintro ⟨m, hm, rfl⟩
      obtain ⟨t, ht⟩ := hB.mem_QK.mp (mem_subgroupOf.mp hm)
      exact ⟨t, by simp only [hρ]; congr 1; exact Subtype.ext ht⟩
    · rintro ⟨t, rfl⟩
      exact ⟨⟨f t, hfM t⟩, mem_subgroupOf.mpr (hB.f_mem_QK t), rfl⟩
  have hρadd : ∀ s t, ρ (s + t) = ρ s * ρ t := by
    intro s t
    simp only [hρ]
    rw [← map_mul]
    congr 1
    exact Subtype.ext (hB.f_add s t)
  have hρ0 : ρ 0 = 1 := by
    simp only [hρ]
    have : (⟨f 0, hfM 0⟩ : M) = 1 := Subtype.ext hB.f_zero
    rw [this, map_one]
  have hρneg : ∀ t, ρ (-t) = (ρ t)⁻¹ := by
    intro t
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← hρadd, neg_add_cancel, hρ0]
  have hρp : ∀ t, ρ t ^ p = 1 := by
    intro t
    simp only [hρ]
    rw [← map_pow]
    have : (⟨f t, hfM t⟩ : M) ^ p = 1 := Subtype.ext (by simpa using hB.f_pow_p t)
    rw [this, map_one]
  have hZelem : IsElemAbelian p Z := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun z hz => ?_⟩
    · obtain ⟨s, hs⟩ := (hZmem a).mp a.2
      obtain ⟨t, ht⟩ := (hZmem b).mp b.2
      apply Subtype.ext
      show (a : M ⧸ O) * b = b * a
      rw [← hs, ← ht, ← hρadd, ← hρadd, add_comm]
    · obtain ⟨t, rfl⟩ := (hZmem z).mp hz
      exact hρp t
  have hZcard : Nat.card Z = p ^ n := by
    have hQp : IsPGroup p (hB.QK.subgroupOf M) := hB.QK_isPGroup.comap_subtype
    rw [hZ, CFSG.AGLEmbedding.card_map_mk_of_isPGroup hpp O (primeComplementCore_coprime p) hQp,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQKM).toEquiv]
    exact hB.card_QK
  have hZc : Z ≤ centralizer ({xb} : Set (M ⧸ O)) := by
    intro z hz
    obtain ⟨t, rfl⟩ := (hZmem z).mp hz
    rw [mem_centralizer_singleton_iff]
    simp only [hρ, hxb]
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hB.f_comm t)
  have hQK2 : 2 ≤ CFSG.Open.pRank p hB.QK := by
    have := CFSG.LocalAnalysis.RankThreeTheoremC.le_pRank_of_elemAbelian_card (p := p) le_rfl
      hB.QK_isElemAbelian hB.card_QK
    have := hB.three_le
    omega
  have hQKN : normalizer (hB.QK : Set G) ≤ M :=
    CFSG.LocalAnalysis.RankFourTheoremC.normalizer_le_of_two_le_pRank hG.fc hloc hB.QK_isPGroup
      hQKM hQK2
  set S : Set (M ⧸ O) := {s | s * xb * s⁻¹ = xb ∧ ∀ z ∈ Z, s * z * s⁻¹ ∈ Z} with hS'
  have hStorus : ∀ a : (GaloisField p n)ˣ, ∃ s ∈ S, ∀ t,
      s * ρ t * s⁻¹ = ρ ((a : GaloisField p n) ^ 2 * t) := by
    intro a
    obtain ⟨g, hgx, hg⟩ := hB.torus a
    have hgN : g ∈ normalizer (hB.QK : Set G) :=
      CFSG.LocalAnalysis.RankFourTheoremC.mem_normalizer_of_map_conj_le (by
        rintro _ ⟨q, hq, rfl⟩
        obtain ⟨t, rfl⟩ := hB.mem_QK.mp hq
        show g * f t * g⁻¹ ∈ hB.QK
        rw [hg]
        exact hB.f_mem_QK _)
    have hgM : g ∈ M := hQKN hgN
    have hs : ∀ t, π ⟨g, hgM⟩ * ρ t * (π ⟨g, hgM⟩)⁻¹ = ρ ((a : GaloisField p n) ^ 2 * t) := by
      intro t
      simp only [hρ]
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hg t)
    refine ⟨π ⟨g, hgM⟩, ⟨?_, fun z hz => ?_⟩, hs⟩
    · simp only [hxb]
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hgx
    · obtain ⟨t, rfl⟩ := (hZmem z).mp hz
      rw [hs t]
      exact (hZmem _).mpr ⟨_, rfl⟩
  have h2 : (2 : GaloisField p n) ≠ 0 := two_ne_zero_galois_p hB.five_le
  have hirr : ∀ D : Subgroup (M ⧸ O), D ≤ Z → (∀ s ∈ S, ∀ d ∈ D, s * d * s⁻¹ ∈ D) →
      D = ⊥ ∨ D = Z := by
    intro D hDZ hDS
    let A : AddSubgroup (GaloisField p n) :=
      { carrier := {t | ρ t ∈ D}
        zero_mem' := by
          show ρ 0 ∈ D
          rw [hρ0]
          exact D.one_mem
        add_mem' := fun {s t} hs ht => by
          show ρ (s + t) ∈ D
          rw [hρadd]
          exact D.mul_mem hs ht
        neg_mem' := fun {t} ht => by
          show ρ (-t) ∈ D
          rw [hρneg]
          exact D.inv_mem ht }
    have hA : ∀ a : (GaloisField p n)ˣ, ∀ t ∈ A, (a : GaloisField p n) ^ 2 * t ∈ A := by
      intro a t ht
      obtain ⟨s, hsS, hs⟩ := hStorus a
      show ρ ((a : GaloisField p n) ^ 2 * t) ∈ D
      rw [← hs t]
      exact hDS s hsS _ ht
    rcases eq_bot_or_eq_top_of_sq h2 A hA with hA0 | hA1
    · left
      refine eq_bot_iff.mpr fun d hd => ?_
      obtain ⟨t, rfl⟩ := (hZmem d).mp (hDZ hd)
      have ht : t ∈ A := hd
      rw [hA0] at ht
      have ht0 : t = 0 := AddSubgroup.mem_bot.mp ht
      rw [ht0, hρ0]
      exact Subgroup.one_mem _
    · right
      refine le_antisymm hDZ fun z hz => ?_
      obtain ⟨t, rfl⟩ := (hZmem z).mp hz
      have ht : t ∈ A := by
        rw [hA1]
        trivial
      exact ht
  set Cx : Subgroup G := centralizer ({x} : Set G) with hCx
  set Ox : Subgroup G := GLBPrimeCore p Cx with hOx
  have hOxM : Ox ≤ M := h.primeCore_le hloc
  set Ob : Subgroup (M ⧸ O) := (Ox.subgroupOf M).map π with hOb
  have hObcop : ¬ p ∣ Nat.card Ob := by
    intro hdvd
    have h1 : Nat.card Ob ∣ Nat.card (Ox.subgroupOf M) :=
      Subgroup.card_dvd_of_surjective (f := π.subgroupMap (Ox.subgroupOf M))
        (π.subgroupMap_surjective _)
    have h2 : Nat.card (Ox.subgroupOf M) = Nat.card Ox :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOxM).toEquiv
    exact (Nat.Prime.coprime_iff_not_dvd hpp).mp (glbPrimeCore_coprime p Cx) (h2 ▸ hdvd.trans h1)
  have hCy : centralizer ({xb} : Set (M ⧸ O)) ≤ ((M ⊓ Cx).subgroupOf M).map π :=
    (CFSG.LocalAnalysis.RankThreeTheoremC.centralizer_mk_le_map hpp hxo').trans
      (Subgroup.map_mono fun c
        (hc : c ∈ centralizer ({(⟨x, hxM⟩ : M)} : Set M)) => mem_subgroupOf.mpr
        ⟨c.2, mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc))⟩)
  have hnormO : centralizer ({xb} : Set (M ⧸ O)) ≤ normalizer (Ob : Set (M ⧸ O)) :=
    hCy.trans (CFSG.LocalAnalysis.RankThreeTheoremC.map_subgroupOf_le_normalizer_map
      (fun c (hc : c ∈ M ⊓ Cx) => le_normalizer_glbPrimeCore p Cx hc.2) π)
  have hZO : Z ⊔ Ob = ((hB.QK ⊔ Ox).subgroupOf M).map π := by
    rw [Subgroup.subgroupOf_sup hQKM hOxM, Subgroup.map_sup]
  have hnormZO : centralizer ({xb} : Set (M ⧸ O)) ≤ normalizer ((Z ⊔ Ob : Subgroup (M ⧸ O)) :
      Set (M ⧸ O)) := by
    rw [hZO]
    exact hCy.trans (CFSG.LocalAnalysis.RankThreeTheoremC.map_subgroupOf_le_normalizer_map
      hB.inf_centralizer_le_normalizer_QK_sup π)
  have hdata : Case2DataP p (M ⧸ O) xb Z S Ob :=
    { base := hbase
      isElemAbelian := hZelem
      card_eq := ⟨n, hB.three_le, hZcard⟩
      le_centralizer := hZc
      centralizes := fun s hs => hs.1
      normalizes := fun s hs => hs.2
      irreducible := hirr
      coprime := hObcop
      normalizes_O := hnormO
      normalizes_ZO := hnormZO }
  have hZp : Z ≤ CFSG.pCore p (M ⧸ O) :=
    Case2DataP.le_pCore hdata hK.hInn hK.hWC hK.h713
  have hPsyl : IsSylowOf p (P : Subgroup G) M := isSylowOf_iff.mpr ⟨hPM, P.isPGroup', fun hdvd =>
    P.not_dvd_index (hdvd.trans (Subgroup.relIndex_dvd_index_of_le hPM))⟩
  obtain ⟨R, hR⟩ : ∃ R : Sylow p (M ⧸ O), (R : Subgroup (M ⧸ O)) =
      ((P : Subgroup G).subgroupOf M).map π := by
    obtain ⟨-, hp', hdvd⟩ := isSylowOf_iff.1 (isSylowOf_top_map_mk hPsyl)
    rw [Subgroup.relIndex_top_right] at hdvd
    exact ⟨hp'.toSylow hdvd, IsPGroup.toSylow_coe _ _⟩
  intro m hm q hq
  obtain ⟨t, rfl⟩ := hB.mem_QK.mp hq
  have hmq : m * f t * m⁻¹ ∈ M := M.mul_mem (M.mul_mem hm (hfM t)) (M.inv_mem hm)
  have hcj : π ⟨m * f t * m⁻¹, hmq⟩ = π ⟨m, hm⟩ * ρ t * (π ⟨m, hm⟩)⁻¹ := by
    simp only [hρ]
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hpc : π ⟨m * f t * m⁻¹, hmq⟩ ∈ CFSG.pCore p (M ⧸ O) := by
    rw [hcj]
    exact (CFSG.pCore_normal (p := p) (G := M ⧸ O)).conj_mem _ (hZp ((hZmem _).mpr ⟨t, rfl⟩)) _
  have hpR : π ⟨m * f t * m⁻¹, hmq⟩ ∈ (R : Subgroup (M ⧸ O)) :=
    CFSG.pCore_isPGroup.le_sylow_of_normal R hpc
  rw [hR] at hpR
  obtain ⟨p', hp', hp'eq⟩ := hpR
  have hp'P : (p' : G) ∈ (P : Subgroup G) := mem_subgroupOf.mp hp'
  have hr : (p' : G)⁻¹ * (m * f t * m⁻¹) ∈ M := M.mul_mem (M.inv_mem p'.2) hmq
  have hker : π ⟨(p' : G)⁻¹ * (m * f t * m⁻¹), hr⟩ = 1 := by
    have e : (⟨(p' : G)⁻¹ * (m * f t * m⁻¹), hr⟩ : M) = p'⁻¹ * ⟨m * f t * m⁻¹, hmq⟩ := rfl
    rw [e, map_mul, map_inv, hp'eq, inv_mul_cancel]
  have hrO := mem_glbPrimeCore_of_mk_eq_one_p hr hker
  have : m * f t * m⁻¹ = (p' : G) * ((p' : G)⁻¹ * (m * f t * m⁻¹)) := by group
  rw [this]
  exact Subgroup.mul_mem _ (mem_sup_left hp'P) (mem_sup_right hrO)

end CFSG.LocalAnalysis.RankFourTheoremC.P5
