module

public import CFSG.GH74.Generic.BProg.B3.S1FinalK1
public import CFSG.GH74.Generic.BProg.B3.S1DiagAct
public import CFSG.GH74.Generic.BProg.B3.FalseCtxS45Comp

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S1FinalK2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.TwoThin CFSG.GH74.Generic
  CFSG.GH74.Generic.S3 CFSG.GH74.Generic.BProg CFSG.Blueprint CFSG.GH74.L5U5 Subgroup
open CFSG.GH74.Generic.BProg.B1.PilotS5 CFSG.GH74.Generic.BProg.B1.PilotS1
open CFSG.GH74.Generic.BProg.B3.S1FinalK1
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G] {x : G} {K A : Subgroup G} {a : G} {D J : Subgroup G}
  {J₁ J₂ : Subgroup G}

omit [Finite G] in
theorem map_conj_eq_of_mem_normalizer {H : Subgroup G} {g : G} (hg : g ∈ normalizer (H : Set G)) :
    H.map (MulAut.conj g).toMonoidHom = H :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp hg

theorem s1_K_side (hc : Ctx21 G x K A a D J)
    (h1 : B1.PilotS1.QShape1Big (↥K ⧸ pPrimeCore 2 ↥K)) (hax : a ≠ x)
    (hS : S1SplitMod K A x a J₁ J₂) {d : G} (hd2 : d * d = 1) (hdA : ∀ e ∈ A, d * e = e * d)
    (hdJ₁ : ∀ j ∈ J₁, ⁅d, j⁆ ∈ pPrimeCoreOf 2 (centralizer ({a} : Set G))) :
    ∃ e ∈ A, e⁻¹ * d ∈ centralizerSection J₂ (pPrimeCoreOf 2 J₂) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, _, F0, _, _, z₀, ⟨eP⟩, hodd0, hbig0, hP⟩ := B1.PilotS1.exists_grpS1_of_big h1
  have hx2 : orderOf x = 2 := hc.circ.1.1.1.1
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := hc.circ.1.1.1.2.2
  obtain ⟨hxK, -, -, hY, hCY, he8⟩ := B1.PilotS1.shape1_data hc.hyp.gen4 hx2 hK eP hP
    (B1.PilotS1.QShape1Big.qShape1 h1)
  obtain ⟨hAK, hAel, hA8⟩ := B1.PilotS1.source_le hxK hc.src
  obtain ⟨hxA, -⟩ := B1.PilotS1.exists_y_of_e8 hx2 hK he8 hAK hAel hA8
  have hKC : K ≤ centralizer ({x} : Set G) := hK.1
  have hAsq : ∀ c ∈ A, c * c = 1 := fun c hc' => by
    rw [← pow_two]; exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) c hc'
  have haA : a ∈ A := hc.a_mem
  have haK : a ∈ K := hAK haA
  have ha2 : orderOf a = 2 := hc.obs.y_ord
  have haC : a ∈ centralizer ({x} : Set G) := hKC haK
  obtain ⟨hub, hub1, hub2⟩ := bar_facts hKC haK ha2
  have hxC : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hAcomm : ∀ c ∈ A, ∀ d ∈ A, c * d = d * c := fun c hc' d hd =>
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥A)).comm ⟨c, hc'⟩ ⟨d, hd⟩)
  have hubx : bar x a ≠ xbar x := by
    intro h
    apply hax
    refine B1.PilotS1.eq_of_proj_eq haC hxC (hAcomm a haA x hxA) (hAsq a haA) (hAsq x hxA) ?_
    rw [← bar_of_mem haC]; exact h
  obtain ⟨F', _, _, hodd', hbig', hSp, hall, hJ₂uniq⟩ := exists_splitAt_bar hc h1 hax hS
  have hdC : d ∈ centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 (hdA x hxA)
  have hdCa : d ∈ centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 (hdA a haA)
  have hconj_fix : ∀ e ∈ A, (MulAut.conj d).toMonoidHom e = e := fun e he => by
    show d * e * d⁻¹ = e
    rw [hdA e he]
    group
  have hdK : d ∈ normalizer (K : Set G) := by
    set K' : Subgroup G := K.map (MulAut.conj d).toMonoidHom with hK'
    have hK'c : IsPCompIn 2 (centralizer ({x} : Set G)) K' :=
      FalseCtxS45Comp.isPCompIn_conj hK hdC
    have haK' : a ∈ K' := ⟨a, haK, hconj_fix a haA⟩
    rcases FalseCtxS45Comp.pCompIn_eq_or_commute hK hK'c with heq | hcomm
    · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq.symm
    · exfalso
      have hcomm' : ⁅PumpCalc.bar x K', PumpCalc.bar x K⁆ = ⊥ :=
        (Subgroup.commutator_comm _ _).trans hcomm
      have hā' : bar x a ∈ PumpCalc.bar x K' := by
        rw [bar_of_mem haC]
        exact ⟨⟨a, haC⟩, Subgroup.mem_subgroupOf.2 haK', rfl⟩
      have hā : bar x a ∈ centralizer ((imgBar x K : Subgroup (CentralizerBar x)) :
          Set (CentralizerBar x)) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm' hā'
      rcases hCY _ hā with h | h
      · exact hub1 h
      · exact hubx h
  have hmapK : K.map (MulAut.conj d).toMonoidHom = K := map_conj_eq_of_mem_normalizer hdK
  have hmapC : (centralizer ({a} : Set G)).map (MulAut.conj d).toMonoidHom =
      centralizer ({a} : Set G) := FalseCtxS45Comp.map_conj_self hdCa
  have hmapHg : (K ⊓ centralizer ({a} : Set G)).map (MulAut.conj d).toMonoidHom =
      K ⊓ centralizer ({a} : Set G) := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj d).injective, hmapK, hmapC]
  have hconj_comp : ∀ L : Subgroup G, IsPCompIn 2 (K ⊓ centralizer ({a} : Set G)) L →
      IsPCompIn 2 (K ⊓ centralizer ({a} : Set G)) (L.map (MulAut.conj d).toMonoidHom) := by
    intro L hL
    have := Stage1.Thm2.Recip.isPCompIn_map_conj hL d
    rwa [hmapHg] at this
  have haJ₁ : a ∈ J₁ := hS.u_mem
  have hJ₁d : J₁.map (MulAut.conj d).toMonoidHom = J₁ := by
    rcases hall _ (hconj_comp J₁ hS.comp₁) with h | h
    · exact h
    · exfalso
      have haJ₂ : a ∈ J₂ := h ▸ (⟨a, haJ₁, hconj_fix a haA⟩ : a ∈ J₁.map (MulAut.conj d).toMonoidHom)
      have : bar x a ∈ imgBar x J₂ := by
        rw [bar_of_mem haC]
        exact mem_imgBar.2 ⟨⟨a, haC⟩, haJ₂, rfl⟩
      exact hub1 (Subgroup.disjoint_def.1 hSp.disj hSp.u_mem this)
  have hJ₂d : J₂.map (MulAut.conj d).toMonoidHom = J₂ := by
    rcases hall _ (hconj_comp J₂ hS.comp₂) with h | h
    · exfalso
      have h' : J₂.map (MulAut.conj d).toMonoidHom = J₁.map (MulAut.conj d).toMonoidHom :=
        h.trans hJ₁d.symm
      exact hS.ne (Subgroup.map_injective (MulAut.conj d).injective h').symm
    · exact h
  have hdJ₁n : d ∈ normalizer (J₁ : Set G) := Subgroup.mem_normalizer_iff_map_conj_eq.mpr hJ₁d
  have hdJ₂n : d ∈ normalizer (J₂ : Set G) := Subgroup.mem_normalizer_iff_map_conj_eq.mpr hJ₂d
  set d' : CentralizerBar x := proj x ⟨d, hdC⟩ with hd'
  have hd'N : d' ∈ normalizer ((imgBar x K : Subgroup (CentralizerBar x)) :
      Set (CentralizerBar x)) := ObsPump.bar_mem_normalizer hKC hdC hdK
  have hd'2 : d' * d' = 1 := by
    rw [hd', ← map_mul]
    have : (⟨d, hdC⟩ : ↥(centralizer ({x} : Set G))) * ⟨d, hdC⟩ = 1 := Subtype.ext hd2
    rw [this, map_one]
  set δ : MulAut ↥(imgBar x K) :=
    CFSG.LocalAnalysis.ComponentInitial.normalizerConjHom (imgBar x K) ⟨d', hd'N⟩ with hδ
  have hδval : ∀ y : ↥(imgBar x K),
      ((δ y : ↥(imgBar x K)) : CentralizerBar x) = d' * y * d'⁻¹ := fun y => rfl
  have hδδ : δ * δ = 1 := by
    rw [hδ, ← map_mul]
    have : (⟨d', hd'N⟩ : ↥(normalizer ((imgBar x K : Subgroup (CentralizerBar x)) :
        Set (CentralizerBar x)))) * ⟨d', hd'N⟩ = 1 := Subtype.ext hd'2
    rw [this, map_one]
  obtain ⟨eK⟩ := B1.PilotS5.hat_equiv_imgBar hK
  have hQ : QShape1 ↥(imgBar x K) :=
    IsSL4Model.of_mulEquiv (B1.PilotS1.QShape1Big.qShape1 h1) eK
  have hAC : A ≤ centralizer ({x} : Set G) := fun g hg => hKC (hAK hg)
  have hrestr_inj : Function.Injective (restrBar hAC) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hg1 : proj x ⟨(g : G), hAC g.2⟩ = 1 := congrArg Subtype.val hg
    have hmem : (⟨(g : G), hAC g.2⟩ : ↥(centralizer ({x} : Set G))) ∈
        pPrimeCore 2 ↥(centralizer ({x} : Set G)) := (QuotientGroup.eq_one_iff _).1 hg1
    have hsq : (⟨(g : G), hAC g.2⟩ : ↥(centralizer ({x} : Set G))) * ⟨(g : G), hAC g.2⟩ = 1 :=
      Subtype.ext (hAsq g g.2)
    have h3 := Th2.Bal.eq_one_of_sq_of_mem_pPrimeCore hsq hmem
    have h4 := congrArg (Subtype.val : ↥(centralizer ({x} : Set G)) → G) h3
    exact Subtype.ext h4
  have hAbar8 : Nat.card ↥(imgBar x A) = 8 := by
    rw [← hA8]
    exact (Nat.card_congr (MulEquiv.ofBijective (restrBar hAC)
      ⟨hrestr_inj, restrBar_surjective hAC⟩).toEquiv).symm
  have hAbarel : CFSG.IsElementaryAbelian 2 ↥(imgBar x A) := by
    have := hAel
    have : CFSG.IsElementaryAbelian 2 ↥(A.subgroupOf (centralizer ({x} : Set G))) :=
      IsElementaryAbelian.subgroupOf hAC
    exact IsElementaryAbelian.map (proj x)
  have hAbarK : imgBar x A ≤ imgBar x K := fun c hc' => by
    obtain ⟨g, hg, rfl⟩ := mem_imgBar.1 hc'
    exact mem_imgBar.2 ⟨g, hAK hg, rfl⟩
  set Ab : Subgroup ↥(imgBar x K) := (imgBar x A).subgroupOf (imgBar x K) with hAb
  have hAbe : CFSG.IsElementaryAbelian 2 ↥Ab := by
    have := hAbarel
    exact IsElementaryAbelian.subgroupOf hAbarK
  have hAb8 : Nat.card ↥Ab = 8 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAbarK).toEquiv).trans hAbar8
  have hxbar : xbar x ∈ imgBar x K := hY.z_mem
  have hbarA : bar x a ∈ imgBar x A := by
    rw [bar_of_mem haC]
    exact mem_imgBar.2 ⟨⟨a, haC⟩, haA, rfl⟩
  have huA : (⟨bar x a, hub⟩ : ↥(imgBar x K)) ∈ Ab := Subgroup.mem_subgroupOf.2 hbarA
  have hSp' := S1FinalK1.SplitAt.of_subtype hSp hxbar hub
  have hzc : ∀ g : ↥(imgBar x K), g * (⟨xbar x, hxbar⟩ : ↥(imgBar x K)) =
      ⟨xbar x, hxbar⟩ * g := fun g => Subtype.ext (xbar_comm x g.1)
  have hF5 : 5 ≤ Nat.card F' := by
    obtain ⟨k, hk⟩ := hodd'
    omega
  have hδA : ∀ e ∈ Ab, δ e = e := by
    intro e he
    have he' : (e : CentralizerBar x) ∈ imgBar x A := Subgroup.mem_subgroupOf.1 he
    obtain ⟨g, hgA, hg⟩ := mem_imgBar.1 he'
    apply Subtype.ext
    rw [hδval]
    show d' * (e : CentralizerBar x) * d'⁻¹ = e
    rw [← hg, hd', mul_inv_eq_iff_eq_mul, ← map_mul, ← map_mul]
    exact congrArg (proj x) (Subtype.ext (hdA g hgA))
  have hJ₁Ca : J₁ ≤ centralizer ({a} : Set G) := hS.comp₁.1.trans inf_le_right
  have hJ₁C : J₁ ≤ centralizer ({x} : Set G) := hS.comp₁.1.trans (inf_le_left.trans hKC)
  have hJ₂C : J₂ ≤ centralizer ({x} : Set G) := hS.comp₂.1.trans (inf_le_left.trans hKC)
  obtain ⟨e₁⟩ := hSp.equiv₁
  have hNodd : Odd (Nat.card (pPrimeCore 2 ↥J₁)) :=
    Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have hδJ : ∀ g ∈ (imgBar x J₁).subgroupOf (imgBar x K), δ g = g := by
    intro g hg
    obtain ⟨j, hjJ, hj⟩ := mem_imgBar.1 (Subgroup.mem_subgroupOf.1 hg)
    have hm1 := hdJ₁ (j : G) hjJ
    have hmJ₁ : ⁅d, (j : G)⁆ ∈ J₁ := by
      have h1 : d * (j : G) * d⁻¹ ∈ J₁ := (Subgroup.mem_normalizer_iff.1 hdJ₁n _).1 hjJ
      have : ⁅d, (j : G)⁆ = (d * (j : G) * d⁻¹) * (j : G)⁻¹ := by
        simp only [commutatorElement_def]
      rw [this]
      exact J₁.mul_mem h1 (J₁.inv_mem hjJ)
    obtain ⟨m', hm', hm'e⟩ := hm1
    have hprojA : proj a m' = 1 := (QuotientGroup.eq_one_iff _).2 hm'
    have hmY : ⁅d, (j : G)⁆ ∈ centralizer ({a} : Set G) := by
      rw [← hm'e]; exact m'.2
    have hm2 : ⁅d, (j : G)⁆ ∈ pPrimeCoreOf 2 J₁ :=
      mem_pPrimeCoreOf_of_proj_eq_one hJ₁Ca hmJ₁ (by
        have : (⟨⁅d, (j : G)⁆, hJ₁Ca hmJ₁⟩ : ↥(centralizer ({a} : Set G))) = m' :=
          Subtype.ext hm'e.symm
        rw [this]; exact hprojA)
    obtain ⟨n, hn, hne⟩ := hm2
    have hproj := proj_eq_one_of_odd_normal hJ₁C hodd' hF5 e₁ (pPrimeCore 2 ↥J₁) hNodd n hn
    have hcomm : ⁅d', proj x j⁆ = 1 := by
      have e1 : (⟨(n : G), hJ₁C n.2⟩ : ↥(centralizer ({x} : Set G))) =
          ⁅(⟨d, hdC⟩ : ↥(centralizer ({x} : Set G))), (j : ↥(centralizer ({x} : Set G)))⁆ := by
        apply Subtype.ext
        exact hne
      rw [e1, map_commutatorElement] at hproj
      exact hproj
    have hcomm' := commutatorElement_eq_one_iff_mul_comm.1 hcomm
    apply Subtype.ext
    rw [hδval, ← hj]
    exact mul_inv_eq_iff_eq_mul.2 hcomm'
  obtain ⟨e, heAb, he⟩ := sl4_diag_action hQ hAbe hAb8 huA hSp' hzc δ hδδ hδA hδJ
  obtain ⟨g, hgA, hg⟩ := mem_imgBar.1 (Subgroup.mem_subgroupOf.1 heAb)
  refine ⟨(g : G), hgA, ?_⟩
  have hAJ₂ : ∀ c ∈ A, c ∈ normalizer (J₂ : Set G) := fun c hc' => (hS.A_norm hc').2
  have hfn : (g : G)⁻¹ * d ∈ normalizer (J₂ : Set G) :=
    (normalizer (J₂ : Set G)).mul_mem ((normalizer (J₂ : Set G)).inv_mem (hAJ₂ _ hgA)) hdJ₂n
  refine ⟨hfn, TwoThin.mem_normalizer_pPrimeCoreOf hfn, fun k hk => ?_⟩
  have hfC : (g : G)⁻¹ * d ∈ centralizer ({x} : Set G) :=
    (centralizer ({x} : Set G)).mul_mem ((centralizer ({x} : Set G)).inv_mem g.2) hdC
  have hkC : k ∈ centralizer ({x} : Set G) := hJ₂C hk
  have hcommJ₂ : ⁅k, (g : G)⁻¹ * d⁆ ∈ J₂ := by
    have h1 : ((g : G)⁻¹ * d) * k⁻¹ * ((g : G)⁻¹ * d)⁻¹ ∈ J₂ :=
      (Subgroup.mem_normalizer_iff.1 hfn _).1 (J₂.inv_mem hk)
    have : ⁅k, (g : G)⁻¹ * d⁆ = k * (((g : G)⁻¹ * d) * k⁻¹ * ((g : G)⁻¹ * d)⁻¹) := by
      simp only [commutatorElement_def, mul_assoc]
    rw [this]
    exact J₂.mul_mem hk h1
  refine mem_pPrimeCoreOf_of_proj_eq_one hJ₂C hcommJ₂ ?_
  have hkK : k ∈ K := (hS.comp₂.1 hk).1
  have hyK : proj x ⟨k, hkC⟩ ∈ imgBar x K := mem_imgBar.2 ⟨⟨k, hkC⟩, hkK, rfl⟩
  have hyJ : (⟨proj x ⟨k, hkC⟩, hyK⟩ : ↥(imgBar x K)) ∈ (imgBar x J₂).subgroupOf (imgBar x K) :=
    Subgroup.mem_subgroupOf.2 (mem_imgBar.2 ⟨⟨k, hkC⟩, hk, rfl⟩)
  have hδk := congrArg (Subtype.val : ↥(imgBar x K) → CentralizerBar x) (he _ hyJ)
  rw [hδval] at hδk
  have hcomm_y : ((e : ↥(imgBar x K)) : CentralizerBar x)⁻¹ * d' * proj x ⟨k, hkC⟩ =
      proj x ⟨k, hkC⟩ * (((e : ↥(imgBar x K)) : CentralizerBar x)⁻¹ * d') := by
    calc ((e : ↥(imgBar x K)) : CentralizerBar x)⁻¹ * d' * proj x ⟨k, hkC⟩
        = ((e : ↥(imgBar x K)) : CentralizerBar x)⁻¹ * (d' * proj x ⟨k, hkC⟩ * d'⁻¹) * d' := by
          group
      _ = ((e : ↥(imgBar x K)) : CentralizerBar x)⁻¹ *
          (((e : ↥(imgBar x K)) : CentralizerBar x) * proj x ⟨k, hkC⟩ *
            ((e : ↥(imgBar x K)) : CentralizerBar x)⁻¹) * d' := by
          rw [show d' * proj x ⟨k, hkC⟩ * d'⁻¹ = ((e : ↥(imgBar x K)) : CentralizerBar x) *
            proj x ⟨k, hkC⟩ * ((e : ↥(imgBar x K)) : CentralizerBar x)⁻¹ from hδk]
      _ = proj x ⟨k, hkC⟩ * (((e : ↥(imgBar x K)) : CentralizerBar x)⁻¹ * d') := by group
  have hfproj : proj x ⟨(g : G)⁻¹ * d, hfC⟩ =
      ((e : ↥(imgBar x K)) : CentralizerBar x)⁻¹ * d' := by
    have : (⟨(g : G)⁻¹ * d, hfC⟩ : ↥(centralizer ({x} : Set G))) = g⁻¹ * ⟨d, hdC⟩ := rfl
    rw [this, map_mul, map_inv, hg]
  show proj x ⁅(⟨k, hkC⟩ : ↥(centralizer ({x} : Set G))), ⟨(g : G)⁻¹ * d, hfC⟩⁆ = 1
  rw [map_commutatorElement, hfproj]
  exact commutatorElement_eq_one_iff_mul_comm.2 hcomm_y.symm

end S1FinalK2

end CFSG.GH74.Generic.BProg.B3
