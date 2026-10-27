module

public import CFSG.ClassicalInvolution.Q3.Q3T6FusL3SqT
public import CFSG.ClassicalInvolution.Q3.Q3T6FusL3Sec
public import CFSG.ClassicalInvolution.Q3.Q3T6FusL3Act
public import CFSG.ClassicalInvolution.Q3.Q3T6FusMain
public import CFSG.ClassicalInvolution.Q3.Q3T6FaFact
public import CFSG.ClassicalInvolution.Q3.Q3T6CoreExact
public import CFSG.ClassicalInvolution.AschTight.S19TF1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.Assembly.LowTwoRank

section Main



variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G} {S : Sylow 2 G}
  {W L : Subgroup G} {t : G} {V : Subgroup G}

namespace FL3Facts

variable {hd : Sec19DataT3 K z S W L t V} (hF : FL3Facts hd)

include hF

theorem fusSec3 {x : G} (hx : x ∈ S19B.sec19BPrime K S W L) :
    FusSec3 K z (Subgroup.centralizer ({x} : Set G)) := by
  have hxS : x ∈ (S : Subgroup G) := hx.1.1.1
  have hx2 : IsPGroup 2 (Subgroup.zpowers x) := S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hxS)
  have hxK : x ∈ centralizerModOdd ⊤ K := hF.CK hxS hx.1.1.2
  have hzx : z ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (hd.hSz hxS)).symm
  exact FusSec3.of_cStar_element (isClassicalMember3_iff_U.mpr hd.tight.member) hd.tight.hyp
    hd.tight.edgeless hd.tight.centralizer_le_normalizer hx2 hxK hzx

end FL3Facts

namespace FusSec3

variable {C : Subgroup G} (h : FusSec3 K z C)

include h

theorem exists_model {t : StatedLieTag} {k : ℕ}
    (hsec : SectionLieTypeU 3 1 (conjFamily (secL K C)) (conjGen (secL K C)) t k) :
    (∃ e, Nonempty (Ih8Model 3 1 (fusΦ K C) t k e)) ∧
      ∀ L' ∈ fusΦ K C, classicalInvolutionOddCore ↥L' = ⊥ := by
  obtain ⟨D, e, he, hft, hadm, hc⟩ := hsec
  have hconj : ConjInvariant (fusΦ K C) := conjInvariant_oddQuotientFamily
    (hypOmegaModU_restrict h.hypC (conjGen (secL K C))).conjInvariant
  exact ⟨⟨e, ⟨ih8ModelOfSystemU D 0 hconj hft hadm he hc⟩⟩,
    oddCore_eq_bot_of_system D (sectionFamily_classical h.hypC)⟩

end FusSec3

namespace FL3Facts

variable {hd : Sec19DataT3 K z S W L t V} (hF : FL3Facts hd)

include hF

theorem exists_conj_of_mem_S3 {x : G} (hx : x ∈ S19B.sec19BPrime K S W L)
    [IsSimpleGroup (fusE K (Subgroup.centralizer ({x} : Set G)))] {tg : StatedLieTag} {k e' : ℕ}
    (M : Ih8Model 3 1 (fusΦ K (Subgroup.centralizer ({x} : Set G))) tg k e')
    (htg : (tg = .PSL ∧ k = 3) ∨ (tg = .PSU ∧ k = 3))
    (hO : oddCoreOf (secImg (conjGen (secL K (Subgroup.centralizer ({x} : Set G))))
      (secL K (Subgroup.centralizer ({x} : Set G)))) = ⊥)
    (s : ↥(Subgroup.centralizer ({x} : Set G))) (hsS : (s : G) ∈ (S : Subgroup G)) {g : G}
    (hsg : (s : G) = g * z * g⁻¹) (hsz : (s : G) * z = z * (s : G)) :
    ∃ e : fusE K (Subgroup.centralizer ({x} : Set G)),
      secAct (conjGen (secL K (Subgroup.centralizer ({x} : Set G)))) s = MulAut.conj e := by
  have hΩ := hF.hypGen
  have hI := hd.tight.isUniqueInvolution
  have hcomm := hF.comm
  have htW : t ∈ W := hd.leW hd.memT
  have hzW := hF.hzW
  have hxS : x ∈ (S : Subgroup G) := hx.1.1.1
  have hxW : x ∈ Subgroup.centralizer (W : Set G) := hx.1.2
  have hzx : z ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (hd.hSz hxS)).symm
  have h := hF.fusSec3 hx
  have hsx : (s : G) * x = x * (s : G) := Subgroup.mem_centralizer_singleton_iff.mp s.2
  have hLY : secL K (Subgroup.centralizer ({x} : Set G)) ≤
      conjGen (secL K (Subgroup.centralizer ({x} : Set G))) := le_conjGen ⟨1, conjSub_one _⟩
  have hzY : ∀ n : ↥(Subgroup.centralizer ({x} : Set G)),
      n * (⟨z, hzx⟩ : ↥(Subgroup.centralizer ({x} : Set G))) * n⁻¹ ∈
        conjGen (secL K (Subgroup.centralizer ({x} : Set G))) :=
    fun n => le_conjGen ⟨n, rfl⟩ (h.isUniqueInvolution_conj_sec n).mem
  have hinner : (∃ n ∈ Subgroup.centralizer ({x} : Set G), n * z * n⁻¹ = (s : G)) →
      ∃ e : fusE K (Subgroup.centralizer ({x} : Set G)),
        secAct (conjGen (secL K (Subgroup.centralizer ({x} : Set G)))) s = MulAut.conj e := by
    rintro ⟨n, hn, he⟩
    have hsY : s ∈ conjGen (secL K (Subgroup.centralizer ({x} : Set G))) := by
      have e : s = ⟨n, hn⟩ * (⟨z, hzx⟩ : ↥(Subgroup.centralizer ({x} : Set G))) * ⟨n, hn⟩⁻¹ :=
        Subtype.ext (by simp [he])
      rw [e]
      exact hzY _
    exact ⟨_, secAct_of_mem _ hsY⟩
  have hs2 : (s : G) * (s : G) = 1 := by
    rw [hsg]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hI.sq]; group
  have hsN : (s : G) ∈ Subgroup.normalizer (W : Set G) := hF.SW hsS
  have hstW : (s : G) * t * (s : G)⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hsN t).mp htW
  have hst2 : (s : G) * t * (s : G)⁻¹ * ((s : G) * t * (s : G)⁻¹) = 1 := by
    calc (s : G) * t * (s : G)⁻¹ * ((s : G) * t * (s : G)⁻¹) = (s : G) * (t * t) * (s : G)⁻¹ := by
          group
      _ = 1 := by rw [hd.invL.sq]; group
  have hst1 : (s : G) * t * (s : G)⁻¹ ≠ 1 := by
    intro h'
    apply hd.invL.ne_one
    calc t = (s : G)⁻¹ * ((s : G) * t * (s : G)⁻¹) * (s : G) := by group
      _ = 1 := by rw [h']; group
  rcases hF.invol_mem_W hstW hst2 hst1 with h' | h' | h'
  · exfalso
    apply hd.ne
    calc t = (s : G)⁻¹ * ((s : G) * t * (s : G)⁻¹) * (s : G) := by group
      _ = z := by rw [h', mul_assoc, ← hsz, inv_mul_cancel_left]
  ·
    apply hinner
    have hst : (s : G) * t = t * (s : G) := by
      calc (s : G) * t = (s : G) * t * (s : G)⁻¹ * (s : G) := by group
        _ = t * (s : G) := by rw [h']
    rw [hsg] at hsx hsz hst ⊢
    exact hF.exists_conj_eq_of_comm_t3 hx hsx hsz hst
  have hsne : (s : G) ≠ z := by
    intro he
    rw [he] at h'
    have h1 : z * t * z⁻¹ = t := by rw [hcomm z hzW t htW, mul_inv_cancel_right]
    rw [h1] at h'
    exact hI.ne_one (mul_left_cancel (a := t) (by rw [mul_one]; exact h'.symm))
  obtain ⟨-, -, -, -, -, -, hcyc, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hF.UKW
  obtain ⟨u, huU, huu⟩ := exists_mul_self_eq_of_isCyclic hI inf_le_left hcyc
    (S.isPGroup'.to_le (inf_le_right.trans hd.hWS)) h4
  have hzU : IsUniqueInvolution (K ⊓ W) z :=
    ⟨⟨hI.mem, hzW⟩, hI.ne_one, hI.sq, fun y hy hy2 => hI.unique y hy.1 hy2⟩
  have hsK : (s : G) ∈ Subgroup.normalizer (K : Set G) :=
    hd.tight.centralizer_le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hsz)
  have hsuU : (s : G) * u * (s : G)⁻¹ ∈ K ⊓ W :=
    ⟨(Subgroup.mem_normalizer_iff.mp hsK u).mp huU.1,
      (Subgroup.mem_normalizer_iff.mp hsN u).mp huU.2⟩
  have hszs : (s : G) * z * (s : G)⁻¹ = z := by rw [hsz, mul_inv_cancel_right]
  have hsuu : (s : G) * u * (s : G)⁻¹ * ((s : G) * u * (s : G)⁻¹) = z := by
    calc (s : G) * u * (s : G)⁻¹ * ((s : G) * u * (s : G)⁻¹) = (s : G) * (u * u) * (s : G)⁻¹ := by
          group
      _ = z := by rw [huu, hszs]
  rcases S1916.eq_or_eq_inv_of_mul_self_eq hzU (fun a ha b hb => hcomm a ha.2 b hb.2) hsuU huU
    hsuu huu with h'' | h''
  ·
    apply hinner
    have hus : u * (s : G) = (s : G) * u := by
      calc u * (s : G) = (s : G) * u * (s : G)⁻¹ * (s : G) := by rw [h'']
        _ = (s : G) * u := by group
    rw [hsg] at hsx hsne hus ⊢
    exact hF.exists_conj_eq_of_comm_u3 hx hsx hsne huU.1
      (S19T.orderOf_eq_four huu hI.ne_one hI.sq) hus
  have hux : u * x = x * u := Subgroup.mem_centralizer_iff.mp hxW u huU.2
  have htx : t * x = x * t := Subgroup.mem_centralizer_iff.mp hxW t htW
  have hut : u * t = t * u := hcomm u huU.2 t htW
  have hζx : u * t ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc u * t * x = u * (t * x) := by group
      _ = (u * x) * t := by rw [htx]; group
      _ = x * (u * t) := by rw [hux]; group
  have hζS : u * t ∈ (S : Subgroup G) := Subgroup.mul_mem _ (hd.hWS huU.2) (hd.hWS htW)
  have hζK : u * t ∈ centralizerModOdd ⊤ K := hF.CK hζS (hF.mul_t_mem_centralizer3 huU huu)
  have hζz : u * t * z = z * (u * t) := hcomm _ (W.mul_mem huU.2 htW) z hzW
  have hζs : (s : G) * (u * t) * (s : G)⁻¹ = u * t := by
    calc (s : G) * (u * t) * (s : G)⁻¹ =
          ((s : G) * u * (s : G)⁻¹) * ((s : G) * t * (s : G)⁻¹) := by group
      _ = u⁻¹ * (z * t) := by rw [h'', h', hcomm t htW z hzW]
      _ = u⁻¹ * (u * u) * t := by rw [huu]; group
      _ = u * t := by group
  have hζζ : u * t * (u * t) = z := by
    calc u * t * (u * t) = u * (t * u) * t := by group
      _ = u * u * (t * t) := by rw [← hut]; group
      _ = z := by rw [huu, hd.invL.sq, mul_one]
  have huKx : (⟨u, Subgroup.mem_centralizer_singleton_iff.mpr hux⟩ :
      ↥(Subgroup.centralizer ({x} : Set G))) ∈
        secL K (Subgroup.centralizer ({x} : Set G)) :=
    Subgroup.mem_subgroupOf.mpr ⟨huU.1, Subgroup.mem_centralizer_singleton_iff.mpr hux⟩
  have huY := hLY huKx
  obtain ⟨h₁, hh₁, he₁⟩ := hF.exists_conj_eq_t3 hx
  have htY : (⟨t, Subgroup.mem_centralizer_singleton_iff.mpr htx⟩ :
      ↥(Subgroup.centralizer ({x} : Set G))) ∈
        conjGen (secL K (Subgroup.centralizer ({x} : Set G))) := by
    have e : (⟨t, Subgroup.mem_centralizer_singleton_iff.mpr htx⟩ :
        ↥(Subgroup.centralizer ({x} : Set G))) =
          ⟨h₁, hh₁⟩ * (⟨z, hzx⟩ : ↥(Subgroup.centralizer ({x} : Set G))) * ⟨h₁, hh₁⟩⁻¹ :=
      Subtype.ext (by simp [he₁])
    rw [e]
    exact hzY _
  have hζY : (⟨u * t, hζx⟩ : ↥(Subgroup.centralizer ({x} : Set G))) ∈
      conjGen (secL K (Subgroup.centralizer ({x} : Set G))) :=
    Subgroup.mul_mem _ huY htY
  set c : fusE K (Subgroup.centralizer ({x} : Set G)) :=
    QuotientGroup.mk ⟨⟨u * t, hζx⟩, hζY⟩ with hc
  have hKΦ : secImg (conjGen (secL K (Subgroup.centralizer ({x} : Set G))))
      (secL K (Subgroup.centralizer ({x} : Set G))) ∈
        fusΦ K (Subgroup.centralizer ({x} : Set G)) :=
    (mem_secFamily_iff _ _).mpr ⟨1, by rw [conjSub_one]⟩
  have hφ2 : secAct (conjGen (secL K (Subgroup.centralizer ({x} : Set G)))) s *
      secAct (conjGen (secL K (Subgroup.centralizer ({x} : Set G)))) s = 1 := by
    rw [← map_mul, show s * s = 1 from Subtype.ext hs2, map_one]
  have hφL : (secImg (conjGen (secL K (Subgroup.centralizer ({x} : Set G))))
      (secL K (Subgroup.centralizer ({x} : Set G)))).map
        (secAct (conjGen (secL K (Subgroup.centralizer ({x} : Set G)))) s).toMonoidHom =
      secImg (conjGen (secL K (Subgroup.centralizer ({x} : Set G))))
        (secL K (Subgroup.centralizer ({x} : Set G))) := by
    rw [secAct_secImg _ s hLY, conjSub_eq_of_mem_normalizer (h.mem_normalizer_sec hsz)]
  have hcC : c ∈ Subgroup.centralizer ((secImg (conjGen (secL K (Subgroup.centralizer
      ({x} : Set G)))) (secL K (Subgroup.centralizer ({x} : Set G))) :
        Subgroup (fusE K (Subgroup.centralizer ({x} : Set G)))) :
          Set (fusE K (Subgroup.centralizer ({x} : Set G)))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hfix := h.secAct_fixes_of_mem_cStar hO (y := ⟨u * t, hζx⟩) hζz hζK y hy
    rw [secAct_of_mem _ hζY, MulAut.conj_apply] at hfix
    calc y * c = c * y * c⁻¹ * c := by rw [hfix]
      _ = c * y := by group
  have hcφ : secAct (conjGen (secL K (Subgroup.centralizer ({x} : Set G)))) s c = c := by
    rw [hc, secAct_mk]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    simp only [MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hζs
  have hcc : c * c ≠ 1 := by
    intro h1
    rw [hc, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff] at h1
    apply (h.isUniqueInvolution_secImg 1).ne_one
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    convert h1 using 1
    apply Subtype.ext
    apply Subtype.ext
    simp [hζζ]
  exact exists_conj_of_fixes_three htg M hKΦ _ hφ2 hφL ⟨c, hcC, hcφ, hcc⟩

end FL3Facts

theorem residual_of_FL3_aux (hd : Sec19DataT3 K z S W L t V)
    (hF : ∀ (S' : Sylow 2 G) (hd' : Sec19DataT3 K z S' W L t V), FL3Facts hd') {x : G}
    (hx : x ∈ S19B.sec19BPrime K S W L) {tg : StatedLieTag}
    (htg : (tg = .PSL ∧ (3 : ℕ) = 3) ∨ (tg = .PSU ∧ (3 : ℕ) = 3))
    (hsec : SectionLieTypeU 3 1
      (conjFamily (secL K (Subgroup.centralizer ({x} : Set G))))
      (conjGen (secL K (Subgroup.centralizer ({x} : Set G)))) tg 3) :
    FusResidualL3 K z (Subgroup.centralizer ({x} : Set G)) := by
  intro s hs hsz
  obtain ⟨g, hsg⟩ := hs
  have hF0 := hF S hd
  have h := hF0.fusSec3 hx
  obtain ⟨⟨e', ⟨M⟩⟩, hOfam⟩ := h.exists_model hsec
  have hKΦ : secImg (conjGen (secL K (Subgroup.centralizer ({x} : Set G))))
      (secL K (Subgroup.centralizer ({x} : Set G))) ∈
        fusΦ K (Subgroup.centralizer ({x} : Set G)) :=
    (mem_secFamily_iff _ _).mpr ⟨1, by rw [conjSub_one]⟩
  have hO : oddCoreOf (secImg (conjGen (secL K (Subgroup.centralizer ({x} : Set G))))
      (secL K (Subgroup.centralizer ({x} : Set G)))) = ⊥ := by
    unfold oddCoreOf
    rw [hOfam _ hKΦ, Subgroup.map_bot]
  have hO' := CFSG.ComponentClassification.OddCore.quotient_corefree
    ↥(conjGen (secL K (Subgroup.centralizer ({x} : Set G))))
  have : Nontrivial (fusE K (Subgroup.centralizer ({x} : Set G))) :=
    ⟨⟨_, 1, (h.isUniqueInvolution_secImg 1).ne_one⟩⟩
  have htag : S1911.IsT6Tag tg 3 := by
    rcases htg with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl ⟨h1, rfl⟩
    · exact Or.inr (Or.inl ⟨h1, rfl⟩)
  have hsimple : IsSimpleGroup (fusE K (Subgroup.centralizer ({x} : Set G))) :=
    isSimpleGroup_of_ih8Model (by norm_num) htag M hO'
  have hI := hd.tight.isUniqueInvolution
  have hs2 : (s : G) * (s : G) = 1 := by
    rw [hsg]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hI.sq]; group
  have hs2' : IsPGroup 2 (Subgroup.zpowers (s : G)) :=
    (S19T.isPGroup_zpowers_iff _).mpr ⟨1, by rw [pow_one, sq, hs2]⟩
  obtain ⟨S', hd', hx', c, hc, hcs⟩ := exists_sylow_conj3 hd hx s.2
    (Subgroup.mem_centralizer_singleton_iff.mpr hsz) hs2'
  have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc.2
  set c' : ↥(Subgroup.centralizer ({x} : Set G)) := ⟨c, hc.1⟩ with hc'
  have hcoe : ((c' * s * c'⁻¹ : ↥(Subgroup.centralizer ({x} : Set G))) : G) =
      c * (s : G) * c⁻¹ := rfl
  have hs'g : ((c' * s * c'⁻¹ : ↥(Subgroup.centralizer ({x} : Set G))) : G) =
      (c * g) * z * (c * g)⁻¹ := by
    rw [hcoe, hsg]
    group
  have hs'z : ((c' * s * c'⁻¹ : ↥(Subgroup.centralizer ({x} : Set G))) : G) * z =
      z * ((c' * s * c'⁻¹ : ↥(Subgroup.centralizer ({x} : Set G))) : G) := by
    rw [hcoe]
    have hcz' : c⁻¹ * z * c = z := by rw [mul_assoc, ← hcz, inv_mul_cancel_left]
    calc c * (s : G) * c⁻¹ * z = c * (s : G) * (c⁻¹ * z * c) * c⁻¹ := by group
      _ = c * ((s : G) * z) * c⁻¹ := by rw [hcz']; group
      _ = c * (z * (s : G)) * c⁻¹ := by rw [hsz]
      _ = (c * z) * (s : G) * c⁻¹ := by group
      _ = z * (c * (s : G) * c⁻¹) := by rw [hcz]; group
  obtain ⟨e, he⟩ := (hF S' hd').exists_conj_of_mem_S3 hx' M htg hO (c' * s * c'⁻¹)
    (hcoe ▸ hcs) hs'g hs'z
  have hsecs : secAct (conjGen (secL K (Subgroup.centralizer ({x} : Set G)))) s =
      MulAut.conj (secAct (conjGen (secL K (Subgroup.centralizer ({x} : Set G)))) c'⁻¹ e) := by
    have e1 : s = c'⁻¹ * (c' * s * c'⁻¹) * c' := by group
    rw [e1, map_mul, map_mul, he, ← S19T.mul_conj_mul_inv, map_inv, inv_inv]
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective
    (secAct (conjGen (secL K (Subgroup.centralizer ({x} : Set G)))) c'⁻¹ e)
  rw [← hy] at hsecs
  exact ⟨y, y.2, S19T.residual_of_secAct_eq_conj hsecs⟩

theorem residual_of_FL3 (hd : Sec19DataT3 K z S W L t V)
    (hF : ∀ (S' : Sylow 2 G) (hd' : Sec19DataT3 K z S' W L t V), FL3Facts hd') {x : G}
    (hx : x ∈ S19B.sec19BPrime K S W L) :
    (SectionLieTypeU 3 1 (conjFamily (secL K (Subgroup.centralizer ({x} : Set G))))
        (conjGen (secL K (Subgroup.centralizer ({x} : Set G)))) .PSL 3 ∨
      SectionLieTypeU 3 1 (conjFamily (secL K (Subgroup.centralizer ({x} : Set G))))
        (conjGen (secL K (Subgroup.centralizer ({x} : Set G)))) .PSU 3) →
      FusResidualL3 K z (Subgroup.centralizer ({x} : Set G)) := by
  rintro (hsec | hsec)
  · exact residual_of_FL3_aux hd hF hx (Or.inl ⟨rfl, rfl⟩) hsec
  · exact residual_of_FL3_aux hd hF hx (Or.inr ⟨rfl, rfl⟩) hsec

end Main

end CFSG.ClassicalInvolution.Q3.Q3T6
