module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.NatMultiDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.BaumFactors
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.BlockExclusionT
import CFSG.Quasithin.Background.C126NatDMin
import CFSG.Quasithin.EmptyFaithful.R3c21B
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenFamData
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraBasic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FStarSubnormal
import CFSG.Adapters.GeneralizedFittingTop
import CFSG.Quasithin.EmptyFaithful.R3c21Aux
import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Quasithin.B2F CFSG.Quasithin.E2
open scoped commutatorElement

section Factors

variable {A : Type*} [Group A]

theorem commutator_le_inf_of_le_normalizer {H K : Subgroup A}
    (hHK : H ≤ Subgroup.normalizer (K : Set A)) (hKH : K ≤ Subgroup.normalizer (H : Set A)) :
    ⁅H, K⁆ ≤ H ⊓ K := by
  rw [Subgroup.commutator_le]
  intro h hh k hk
  rw [commutatorElement_def]
  refine ⟨?_, ?_⟩
  · have h1 : k * h⁻¹ * k⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp (hKH hk) h⁻¹).mp (H.inv_mem hh)
    have e : h * k * h⁻¹ * k⁻¹ = h * (k * h⁻¹ * k⁻¹) := by group
    rw [e]
    exact H.mul_mem hh h1
  · have h1 : h * k * h⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hHK hh) k).mp hk
    exact K.mul_mem h1 (K.inv_mem hk)

theorem mem_normalizer_centralizer {S : Subgroup A} {g : A}
    (hg : g ∈ Subgroup.normalizer (S : Set A)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (S : Set A) : Set A) := by
  have key : ∀ g ∈ Subgroup.normalizer (S : Set A), ∀ c ∈ Subgroup.centralizer (S : Set A),
      g * c * g⁻¹ ∈ Subgroup.centralizer (S : Set A) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro s hs
    have hs' : g⁻¹ * s * g ∈ S := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) s).mp hs
      simpa using this
    have h1 := hc _ hs'
    calc s * (g * c * g⁻¹) = g * ((g⁻¹ * s * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * s * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * s := by group
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · exact key g hg c
  · intro h
    have := key g⁻¹ (Subgroup.inv_mem _ hg) _ h
    simpa [mul_assoc] using this

theorem exists_mem_le_of_commutator_ne_bot {I : Finset (Subgroup A)}
    (hcomm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    (hperf : ∀ L ∈ I, ⁅L, L⁆ = L)
    (hsimp : ∀ L ∈ I, ∀ N : Subgroup A, L ≤ Subgroup.normalizer (N : Set A) → L ⊓ N = ⊥ ∨ L ≤ N)
    {Q : Subgroup A} (hSQ : (⨆ L ∈ I, L) ≤ Subgroup.normalizer (Q : Set A))
    (hQS : Q ≤ Subgroup.normalizer ((⨆ L ∈ I, L : Subgroup A) : Set A))
    (hne : ⁅(⨆ L ∈ I, L : Subgroup A), Q⁆ ≠ ⊥) : ∃ L ∈ I, L ≤ Q := by
  set S : Subgroup A := ⨆ L ∈ I, L with hS
  by_contra hno
  push Not at hno
  have hLS : ∀ L ∈ I, L ≤ S := fun L hL => le_iSup₂ (f := fun L (_ : L ∈ I) => L) L hL
  set Q₀ : Subgroup A := Q ⊓ S with hQ₀
  have hSQ₀ : S ≤ Subgroup.normalizer (Q₀ : Set A) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hSQ hx, Subgroup.le_normalizer hx⟩
  have hQ₀L : ∀ L ∈ I, Q₀ ≤ Subgroup.normalizer (L : Set A) := fun L hL =>
    inf_le_right.trans (iSup_le_normalizer_of_commuting hcomm hL)
  have hcent : ∀ L ∈ I, L ≤ Subgroup.centralizer (Q₀ : Set A) := by
    intro L hL
    rcases hsimp L hL Q₀ ((hLS L hL).trans hSQ₀) with h | h
    · have h1 : ⁅L, Q₀⁆ ≤ L ⊓ Q₀ :=
        commutator_le_inf_of_le_normalizer ((hLS L hL).trans hSQ₀) (hQ₀L L hL)
      rw [h] at h1
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 (le_bot_iff.1 h1)
    · exact absurd (h.trans inf_le_left) (hno L hL)
  have hSC : S ≤ Subgroup.centralizer (Q₀ : Set A) := iSup₂_le hcent
  have hQ₀C : Q₀ ≤ Subgroup.centralizer (S : Set A) := Subgroup.le_centralizer_iff.1 hSC
  have hSQ' : ⁅S, Q⁆ ≤ Q₀ := by
    have h := commutator_le_inf_of_le_normalizer hSQ hQS
    rw [hQ₀, inf_comm]
    exact h
  have h1 : ⁅⁅S, Q⁆, S⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hSQ'.trans hQ₀C)
  have h2 : ⁅⁅Q, S⁆, S⁆ = ⊥ := by rw [Subgroup.commutator_comm Q S]; exact h1
  have h3 : ⁅⁅S, S⁆, Q⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  have hSS : S ≤ ⁅S, S⁆ := iSup₂_le fun L hL =>
    (hperf L hL).symm.le.trans (Subgroup.commutator_mono (hLS L hL) (hLS L hL))
  exact hne (le_bot_iff.1 ((Subgroup.commutator_mono_left hSS).trans h3.le))

theorem false_of_perfect_le_commutator [Finite A] {L Q Q' U : Subgroup A} (hperf : ⁅L, L⁆ = L)
    (hL : L ≠ ⊥) (hLQ : L ≤ Q) (hLQ' : L ≤ Q') (hQQ' : ⁅Q, Q'⁆ ≤ U) (hU : IsPGroup 2 U) :
    False := by
  have hLU : L ≤ U :=
    calc L = ⁅L, L⁆ := hperf.symm
      _ ≤ ⁅Q, Q'⁆ := Subgroup.commutator_mono hLQ hLQ'
      _ ≤ U := hQQ'
  have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.2 hperf
  have : Nontrivial ↥L := (Subgroup.nontrivial_iff_ne_bot L).2 hL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Group.IsPerfect.not_isNilpotent ↥L (hU.to_le hLU).isNilpotent

end Factors

section Natural

variable {W : Type*} [CommGroup W]

theorem inf_eq_bot_or_le_of_isL2Natural {L : Subgroup (MulAut W)} {C : Subgroup W} {n : ℕ}
    (h : IsL2Natural L C n) (hn : 2 ≤ n) (N : Subgroup (MulAut W))
    (hLN : L ≤ Subgroup.normalizer (N : Set (MulAut W))) : L ⊓ N = ⊥ ∨ L ≤ N := by
  have : (N.subgroupOf L).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have := (Subgroup.mem_normalizer_iff.mp (hLN g.2) x).mp hx
    simpa using this⟩
  rcases R3c21.eq_bot_or_eq_top_of_isL2Natural h hn (N.subgroupOf L) with h0 | h1
  · left
    rw [eq_bot_iff]
    intro x hx
    have hmem : (⟨x, hx.1⟩ : L) ∈ N.subgroupOf L := hx.2
    rw [h0, Subgroup.mem_bot] at hmem
    exact (Subgroup.mem_bot).2 (congrArg Subtype.val hmem)
  · right
    exact Subgroup.subgroupOf_eq_top.1 h1

theorem ne_bot_of_isL2Natural {L : Subgroup (MulAut W)} {C : Subgroup W} {n : ℕ}
    (h : IsL2Natural L C n) (hn : 2 ≤ n) : L ≠ ⊥ := by
  obtain ⟨-, F, _, _, hF, e, -⟩ := h
  have hs := R3c21.isSimpleGroup_sl2_of_card_two_pow hn hF
  have : IsSimpleGroup ↥L := @MulEquiv.isSimpleGroup _ _ _ _ hs e
  exact (Subgroup.nontrivial_iff_ne_bot L).1 inferInstance

end Natural

section XSide

variable {X : Type} [Group X] {T : Subgroup X}

theorem vZ_le_gnV (T H : Subgroup X) : VZ T H ≤ gnV T := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨h, -, z, hz, rfl⟩
  exact (Subgroup.normalClosure_normal (s := (omegaOneCenterOf T : Set X))).conj_mem z
    (Subgroup.subset_normalClosure hz) h

theorem gnC_le_centralizer_vZ (T H : Subgroup X) :
    gnC T ≤ Subgroup.centralizer (VZ T H : Set X) :=
  Subgroup.centralizer_le (vZ_le_gnV T H)

theorem commutator_ne_bot_of_le_conjClosure {H : Subgroup X} (hTH : T ≤ H)
    (hV : IsElemAbelian 2 (VZ T H)) {S : Subgroup (MulAut (IntMod (VZ T H) hV))}
    (hSn : autI hV H ≤ Subgroup.normalizer (S : Set (MulAut (IntMod (VZ T H) hV))))
    (hSres : S ≤ autI hV (twoResidual H))
    (hSab : ¬ S ≤ Subgroup.centralizer (S : Set (MulAut (IntMod (VZ T H) hV))))
    {C : Subgroup (X ⧸ gnC T)} (hCH : C ≤ gnImg T H)
    (hgen : gnImg T (twoResidual H) ≤ conjClosure C (gnImg T T)) :
    ⁅S, autI hV (H ⊓ C.comap (QuotientGroup.mk' (gnC T)))⁆ ≠ ⊥ := by
  intro h0
  set π := QuotientGroup.mk' (gnC T) with hπ
  have hHN : H ≤ Subgroup.normalizer (VZ T H : Set X) := le_normalizer_conjClosure _ H
  set CS : Subgroup (MulAut (IntMod (VZ T H) hV)) :=
    Subgroup.centralizer (S : Set (MulAut (IntMod (VZ T H) hV))) with hCS
  have hQ : autI hV (H ⊓ C.comap π) ≤ CS :=
    Subgroup.le_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h0)
  set D : Subgroup X := preI hV H hHN CS with hD
  have hDconj : ∀ t ∈ H, ∀ y ∈ D, t * y * t⁻¹ ∈ D := by
    intro t ht y hy
    obtain ⟨hyH, hyC⟩ := (mem_preI hV).1 hy
    have hm : t * y * t⁻¹ ∈ H := H.mul_mem (H.mul_mem ht hyH) (H.inv_mem ht)
    refine (mem_preI hV).2 ⟨hm, ?_⟩
    have e : convHom hV H hHN ⟨t * y * t⁻¹, hm⟩ = convHom hV H hHN ⟨t, ht⟩ *
        convHom hV H hHN ⟨y, hyH⟩ * (convHom hV H hHN ⟨t, ht⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e]
    have hρt : convHom hV H hHN ⟨t, ht⟩ ∈
        Subgroup.normalizer (S : Set (MulAut (IntMod (VZ T H) hV))) :=
      hSn (convI_mem_autI hV ht (hHN ht))
    exact (Subgroup.mem_normalizer_iff.mp (mem_normalizer_centralizer hρt) _).mp hyC
  have hstep : ∀ t ∈ T, ∀ x ∈ H, π x ∈ B6.conjSub (π t) C → x ∈ D := by
    intro t ht x hx hxC
    have htH : t ∈ H := hTH ht
    have hy : t⁻¹ * x * t ∈ H ⊓ C.comap π := by
      refine ⟨H.mul_mem (H.mul_mem (H.inv_mem htH) hx) htH, ?_⟩
      show π (t⁻¹ * x * t) ∈ C
      rw [map_mul, map_mul, map_inv]
      exact B6.mem_conjSub.1 hxC
    have hyD : t⁻¹ * x * t ∈ D :=
      (mem_preI hV).2 ⟨hy.1, hQ (convI_mem_autI hV hy (hHN hy.1))⟩
    have := hDconj t htH _ hyD
    simpa [mul_assoc] using this
  have hcl : conjClosure C (gnImg T T) ≤ D.map π := by
    refine conjClosure_le fun h hh z hz => ?_
    obtain ⟨t, ht, rfl⟩ := hh
    obtain ⟨y, hyH, rfl⟩ := hCH hz
    have hm : t * y * t⁻¹ ∈ H := H.mul_mem (H.mul_mem (hTH ht) hyH) (H.inv_mem (hTH ht))
    refine ⟨t * y * t⁻¹, hstep t ht _ hm ?_, by simp [π, map_mul, map_inv]⟩
    rw [B6.mem_conjSub]
    simpa [π, map_mul, map_inv, mul_assoc] using hz
  have hres : twoResidual H ≤ D := by
    intro x hx
    have hxH : x ∈ H := twoResidual_le H hx
    obtain ⟨d, hd, hdx⟩ := hcl (hgen ⟨x, hx, rfl⟩)
    have hdH : d ∈ H := preI_le hV hd
    have hk : d⁻¹ * x ∈ gnC T := by
      have h1 : (d : X ⧸ gnC T) = (x : X ⧸ gnC T) := hdx
      exact QuotientGroup.eq.1 h1
    have hk' : d⁻¹ * x ∈ H ⊓ Subgroup.centralizer (VZ T H : Set X) :=
      ⟨H.mul_mem (H.inv_mem hdH) hxH, gnC_le_centralizer_vZ T H hk⟩
    have := D.mul_mem hd (inf_centralizer_le_preI hV hk')
    simpa using this
  apply hSab
  refine hSres.trans ((autI_mono hV hres).trans fun φ hφ => ?_)
  obtain ⟨g, hgD, rfl⟩ := (mem_autI hV).1 hφ
  obtain ⟨hgH, hg⟩ := (mem_preI hV).1 hgD
  exact hg

variable [Finite X]

theorem exists_mem_le_autI_of_family {H : Subgroup X} (hTH : T ≤ H)
    (hV : IsElemAbelian 2 (VZ T H)) {J : Finset (Subgroup (MulAut (IntMod (VZ T H) hV)))}
    (hJne : J.Nonempty) (hcomm : ∀ L ∈ J, ∀ L' ∈ J, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    (hperf : ∀ L ∈ J, ⁅L, L⁆ = L) (hne0 : ∀ L ∈ J, L ≠ ⊥)
    (hsimp : ∀ L ∈ J, ∀ N : Subgroup (MulAut (IntMod (VZ T H) hV)),
      L ≤ Subgroup.normalizer (N : Set (MulAut (IntMod (VZ T H) hV))) → L ⊓ N = ⊥ ∨ L ≤ N)
    (hSH : (⨆ L ∈ J, L) ≤ autI hV H)
    (hSn : autI hV H ≤
      Subgroup.normalizer (((⨆ L ∈ J, L) : Subgroup (MulAut (IntMod (VZ T H) hV))) :
        Set (MulAut (IntMod (VZ T H) hV))))
    {C : Subgroup (X ⧸ gnC T)} (hCH : C ≤ gnImg T H)
    (hCN : gnImg T (twoResidual H) ≤ Subgroup.normalizer (C : Set (X ⧸ gnC T)))
    (hgen : gnImg T (twoResidual H) ≤ conjClosure C (gnImg T T)) :
    ∃ L ∈ J, L ≤ autI hV (H ⊓ C.comap (QuotientGroup.mk' (gnC T))) := by
  set π := QuotientGroup.mk' (gnC T) with hπ
  set S : Subgroup (MulAut (IntMod (VZ T H) hV)) := ⨆ L ∈ J, L with hSdef
  have hLS : ∀ L ∈ J, L ≤ S := fun L hL => le_iSup₂ (f := fun L (_ : L ∈ J) => L) L hL
  have hSres : S ≤ autI hV (twoResidual H) := iSup₂_le fun L hL =>
    (C126.Nat.le_twoResidual_of_perfect ((hLS L hL).trans hSH) (hperf L hL)).trans
      (R3c21.twoResidual_autI_le_autI_twoResidual hV)
  have hSab : ¬ S ≤ Subgroup.centralizer (S : Set (MulAut (IntMod (VZ T H) hV))) := by
    intro h
    obtain ⟨L₀, hL₀⟩ := hJne
    apply hne0 L₀ hL₀
    have h1 : ⁅L₀, L₀⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2
      ((hLS L₀ hL₀).trans (h.trans (Subgroup.centralizer_le (hLS L₀ hL₀))))
    rw [← hperf L₀ hL₀, h1]
  set Q : Subgroup (MulAut (IntMod (VZ T H) hV)) := autI hV (H ⊓ C.comap π) with hQdef
  have hON : twoResidual H ≤ Subgroup.normalizer ((H ⊓ C.comap π : Subgroup X) : Set X) := by
    intro g hg
    have hgH : g ∈ H := twoResidual_le H hg
    have hgC : π g ∈ Subgroup.normalizer (C : Set (X ⧸ gnC T)) := hCN ⟨g, hg, rfl⟩
    have hgC' : g ∈ Subgroup.normalizer ((C.comap π : Subgroup X) : Set X) := by
      rw [Subgroup.mem_normalizer_iff] at hgC ⊢
      intro x
      simp only [Subgroup.mem_comap, map_mul, map_inv]
      exact hgC (π x)
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hgH, hgC'⟩
  have hSQ : S ≤ Subgroup.normalizer (Q : Set (MulAut (IntMod (VZ T H) hV))) :=
    hSres.trans (autI_le_normalizer_autI' hV hON)
  have hQS : Q ≤ Subgroup.normalizer (S : Set (MulAut (IntMod (VZ T H) hV))) :=
    (autI_mono hV inf_le_left).trans hSn
  have hne : ⁅S, Q⁆ ≠ ⊥ := commutator_ne_bot_of_le_conjClosure hTH hV hSn hSres hSab hCH hgen
  exact exists_mem_le_of_commutator_ne_bot hcomm hperf hsimp hSQ hQS hne

theorem false_of_le_autI_of_conj {H : Subgroup X} (hV : IsElemAbelian 2 (VZ T H))
    {L : Subgroup (MulAut (IntMod (VZ T H) hV))} (hperf : ⁅L, L⁆ = L) (hne : L ≠ ⊥)
    {C U : Subgroup (X ⧸ gnC T)} (hU : IsPGroup 2 U)
    (hLQ : L ≤ autI hV (H ⊓ C.comap (QuotientGroup.mk' (gnC T))))
    {b : X} (hbH : b ∈ H) (hbN : b ∈ Subgroup.normalizer (VZ T H : Set X))
    (hbL : convI hV ⟨b, hbN⟩ ∈ Subgroup.normalizer (L : Set (MulAut (IntMod (VZ T H) hV))))
    (hbC : ⁅C, B6.conjSub (QuotientGroup.mk' (gnC T) b) C⁆ ≤ U) : False := by
  set π := QuotientGroup.mk' (gnC T) with hπ
  have hHN : H ≤ Subgroup.normalizer (VZ T H : Set X) := le_normalizer_conjClosure _ H
  set Q : Subgroup (MulAut (IntMod (VZ T H) hV)) := autI hV (H ⊓ C.comap π) with hQdef
  have hLb : L.map (MulAut.conj (convI hV ⟨b, hbN⟩)).toMonoidHom = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 hbL
  have hQ' : Q.map (MulAut.conj (convI hV ⟨b, hbN⟩)).toMonoidHom =
      autI hV (cjSub b (H ⊓ C.comap π)) := autI_cjSub hV hbN _
  have hLQ' : L ≤ autI hV (cjSub b (H ⊓ C.comap π)) := by
    rw [← hQ', ← hLb]
    exact Subgroup.map_mono hLQ
  have hcH : cjSub b (H ⊓ C.comap π) ≤ H := cjSub_le (Subgroup.le_normalizer hbH) inf_le_left
  have hcomm : ⁅H ⊓ C.comap π, cjSub b (H ⊓ C.comap π)⁆ ≤ H ⊓ U.comap π := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hyH : y ∈ H := hcH hy
    refine ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem hx.1 hyH) (H.inv_mem hx.1)) (H.inv_mem hyH)
    · have hy' : π y ∈ B6.conjSub (π b) C := by
        rw [B6.mem_conjSub]
        have h1 : π (b⁻¹ * y * b) ∈ C := (mem_cjSub.1 hy).2
        rw [map_mul, map_mul, map_inv] at h1
        exact h1
      have h2 : ⁅π x, π y⁆ ∈ U := hbC (Subgroup.commutator_mem_commutator hx.2 hy')
      show π ⁅x, y⁆ ∈ U
      rw [map_commutatorElement]
      exact h2
  have hQQ' : ⁅Q, autI hV (cjSub b (H ⊓ C.comap π))⁆ ≤ autI hV (H ⊓ U.comap π) := by
    rw [hQdef, ← R3c21.autI_commutator hV (inf_le_left.trans hHN) (hcH.trans hHN)]
    exact autI_mono hV hcomm
  have hU' : IsPGroup 2 ↥(autI hV (H ⊓ U.comap π)) := by
    intro φ
    obtain ⟨g, hg, hgφ⟩ := (mem_autI hV).1 φ.2
    obtain ⟨k, hk⟩ := hU ⟨π g, hg.2⟩
    refine ⟨k, Subtype.ext ?_⟩
    have hk' : π ((g : X) ^ 2 ^ k) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    have hkC : (g : X) ^ 2 ^ k ∈ gnC T := (QuotientGroup.eq_one_iff _).1 hk'
    have h1 : convI hV (g ^ 2 ^ k) = 1 :=
      (convI_eq_one_iff hV _).2 (by
        rw [Subgroup.coe_pow]
        exact gnC_le_centralizer_vZ T H hkC)
    rw [Subgroup.coe_pow, ← hgφ, ← map_pow, h1, OneMemClass.coe_one]
  exact false_of_perfect_le_commutator hperf hne hLQ hLQ' hQQ' hU'

theorem exists_mem_le_autI_of_natural {H : Subgroup X} (hTH : T ≤ H)
    (hV : IsElemAbelian 2 (VZ T H)) {I : Finset (Subgroup (MulAut (IntMod (VZ T H) hV)))}
    (hFam : E23FamGen H T (VZ T H) hV I)
    (hn2 : ∀ L ∈ I, ∃ n : ℕ, 2 ≤ n ∧ IsL2Natural L (fixV (autI hV (twoResidual H))) n)
    {C : Subgroup (X ⧸ gnC T)} (hCH : C ≤ gnImg T H)
    (hCN : gnImg T (twoResidual H) ≤ Subgroup.normalizer (C : Set (X ⧸ gnC T)))
    (hgen : gnImg T (twoResidual H) ≤ conjClosure C (gnImg T T)) :
    ∃ L ∈ I, L ≤ autI hV (H ⊓ C.comap (QuotientGroup.mk' (gnC T))) := by
  have hSJ : autI hV (thompsonJ H) = ⨆ L ∈ I, L := hFam.2.1
  refine exists_mem_le_autI_of_family hTH hV hFam.1 hFam.2.2.1
    (fun L hL => ?_) (fun L hL => ?_) (fun L hL N hLN => ?_) ?_ ?_ hCH hCN hgen
  · obtain ⟨n, hn, h⟩ := hn2 L hL
    exact Subgroup.isPerfect_iff.1 (R3c21.isPerfect_of_isL2Natural h hn)
  · obtain ⟨n, hn, h⟩ := hn2 L hL
    exact ne_bot_of_isL2Natural h hn
  · obtain ⟨n, hn, h⟩ := hn2 L hL
    exact inf_eq_bot_or_le_of_isL2Natural h hn N hLN
  · rw [← hSJ]
    exact autI_mono hV (C1GN.thompsonJ_le H)
  · rw [← hSJ]
    exact autI_le_normalizer_autI' hV
      (Subgroup.le_normalizer.trans (GammaExtra.normalizer_le_normalizer_thompsonJ H))

theorem false_of_baum_comm {H : Subgroup X} (hTH : T ≤ H) (hT : IsSylowTwoOf T H)
    (hV : IsElemAbelian 2 (VZ T H)) {I : Finset (Subgroup (MulAut (IntMod (VZ T H) hV)))}
    (hFam : E23FamGen H T (VZ T H) hV I)
    (hn2 : ∀ L ∈ I, ∃ n : ℕ, 2 ≤ n ∧ IsL2Natural L (fixV (autI hV (twoResidual H))) n)
    {C U : Subgroup (X ⧸ gnC T)} (hCH : C ≤ gnImg T H)
    (hCN : gnImg T (twoResidual H) ≤ Subgroup.normalizer (C : Set (X ⧸ gnC T)))
    (hgen : gnImg T (twoResidual H) ≤ conjClosure C (gnImg T T)) (hU : IsPGroup 2 U)
    {b : X} (hb : b ∈ baum T)
    (hbC : ⁅C, B6.conjSub (QuotientGroup.mk' (gnC T) b) C⁆ ≤ U) : False := by
  obtain ⟨L, hL, hLQ⟩ := exists_mem_le_autI_of_natural hTH hV hFam hn2 hCH hCN hgen
  obtain ⟨n, hn, h⟩ := hn2 L hL
  have hbH : b ∈ H := hTH (C1GN.baum_le T hb)
  have hbN : b ∈ Subgroup.normalizer (VZ T H : Set X) := le_normalizer_conjClosure _ H hbH
  exact false_of_le_autI_of_conj hV (Subgroup.isPerfect_iff.1 (R3c21.isPerfect_of_isL2Natural h hn))
    (ne_bot_of_isL2Natural h hn) hU hLQ hbH hbN
    (convI_baum_mem_normalizer_of_fam hT hFam (Or.inl fun L hL => (hn2 L hL).imp fun _ h => h.2)
      hb hbN hL) hbC

end XSide

section Component

variable {Y : Type*} [Group Y]

theorem isComponentOf_conjSub_top {L : Subgroup Y} (hL : Open.IsComponentOf L ⊤) (t : Y) :
    Open.IsComponentOf (B6.conjSub t L) ⊤ :=
  (CFSG.Adapters.isComponentOf_top_iff _).2
    (CFSG.GorensteinWalter.fstar_isComponentOf_conjugateSubgroup_of_mem
      ((CFSG.Adapters.isComponentOf_top_iff L).1 hL) t (Subgroup.mem_top t))

theorem conjSub_le_centralizer_of_not_mem_normalizer [Finite Y] {L : Subgroup Y}
    (hL : Open.IsComponentOf L ⊤) {t : Y} (ht : t ∉ Subgroup.normalizer (L : Set Y)) :
    B6.conjSub t L ≤ Subgroup.centralizer (L : Set Y) := by
  have hne : B6.conjSub t L ≠ L := fun h =>
    ht (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (CFSG.GorensteinWalter.component_commute_of_ne
      ((CFSG.Adapters.isComponentOf_top_iff _).1 (isComponentOf_conjSub_top hL t))
      ((CFSG.Adapters.isComponentOf_top_iff L).1 hL) hne)

end Component

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

theorem baum_le_gnStab_normalizer (hX : GNSetting X T) {L W : Subgroup (X ⧸ gnC T)}
    (hL : Open.IsComponentOf L ⊤) (hWL : W ≤ L)
    (hRW : gnImg T T ⊓ Subgroup.normalizer (L : Set (X ⧸ gnC T)) ≤
      Subgroup.normalizer (W : Set (X ⧸ gnC T)))
    {H : Subgroup X} (hTH : T ≤ H) (hmap : gnImg T H = conjClosure W (gnImg T T) ⊔ gnImg T T)
    (hV : IsElemAbelian 2 (VZ T H)) {I : Finset (Subgroup (MulAut (IntMod (VZ T H) hV)))}
    (hFam : E23FamGen H T (VZ T H) hV I)
    (hn2 : ∀ L ∈ I, ∃ n : ℕ, 2 ≤ n ∧ IsL2Natural L (fixV (autI hV (twoResidual H))) n) :
    baum T ≤ gnStab T (Subgroup.normalizer (L : Set (X ⧸ gnC T))) := by
  intro b hb
  refine mem_gnStab.2 ⟨C1GN.baum_le T hb, ?_⟩
  by_contra hbL
  have hTp : IsPGroup 2 ↥(gnImg T T) := hX.sylow.2.1.map _
  have hT : IsSylowTwoOf T H := B6.isSylowTwoOf_mono hX.sylow hTH le_top
  have hres : gnImg T (twoResidual H) ≤ conjClosure W (gnImg T T) := by
    show (twoResidual H).map (QuotientGroup.mk' (gnC T)) ≤ _
    rw [E1.map_twoResidual]
    show twoResidual (gnImg T H) ≤ _
    rw [hmap]
    exact twoResidual_sup_le_of_pGroup hTp (le_normalizer_conjClosure W _)
  have hYN : conjClosure W (gnImg T T) ≤ Subgroup.normalizer (W : Set (X ⧸ gnC T)) :=
    conjClosure_le_normalizer_of_component hL hWL hRW hWL Subgroup.le_normalizer
  have hWH : W ≤ gnImg T H := by
    rw [hmap]
    exact (le_conjClosure W _).trans le_sup_left
  refine false_of_baum_comm hTH hT hV hFam hn2 hWH (hres.trans hYN) hres IsPGroup.of_bot hb ?_
  have hc := conjSub_le_centralizer_of_not_mem_normalizer hL hbL
  have h1 : W ≤ Subgroup.centralizer
      (B6.conjSub (QuotientGroup.mk' (gnC T) b) W : Set (X ⧸ gnC T)) :=
    hWL.trans ((Subgroup.le_centralizer_iff.1 hc).trans
      (Subgroup.centralizer_le ((B6.conjSub (QuotientGroup.mk' (gnC T) b)).monotone hWL)))
  exact (Subgroup.commutator_eq_bot_iff_le_centralizer.2 h1).le

theorem baum_le_gnStab_of_natCase (hX : GNSetting X T) {L : Subgroup (X ⧸ gnC T)}
    (hL : Open.IsComponentOf L ⊤) {P : Subgroup (X ⧸ gnC T)}
    (hPb : IsMinOverBorel L (gnImg T T ⊓ L) P) {H₁ : Subgroup X} (hTH : T ≤ H₁)
    (hmap : gnImg T H₁ = conjClosure (pElementSubgroup 2 (conjClosure P
        (gnImg T T ⊓ Subgroup.normalizer (L : Set (X ⧸ gnC T))))) (gnImg T T) ⊔ gnImg T T)
    (hV : IsElemAbelian 2 (VZ T H₁)) (hnat : NatCaseGen H₁ T (VZ T H₁) hV) :
    baum T ≤ gnStab T (Subgroup.normalizer (L : Set (X ⧸ gnC T))) := by
  obtain ⟨-, I, hFam, hn2⟩ := hnat
  set R : Subgroup (X ⧸ gnC T) := gnImg T T ⊓ Subgroup.normalizer (L : Set (X ⧸ gnC T)) with hR
  have hWL : pElementSubgroup 2 (conjClosure P R) ≤ L :=
    (pElementSubgroup_le _).trans (conjClosure_le fun h hh z hz =>
      (Subgroup.mem_normalizer_iff.mp hh.2 z).mp (hPb.1 hz))
  have hRW : R ≤ Subgroup.normalizer (pElementSubgroup 2 (conjClosure P R) : Set (X ⧸ gnC T)) :=
    (le_normalizer_conjClosure P R).trans (normalizer_le_normalizer_pElementSubgroup 2 _)
  exact baum_le_gnStab_normalizer hX hL hWL hRW hTH hmap hV hFam hn2

theorem baum_le_gnStab_of_le_normalizer (hX : GNSetting X T) {L : Subgroup (X ⧸ gnC T)}
    (hL : Open.IsComponentOf L ⊤) {P : Subgroup (X ⧸ gnC T)}
    (hPb : IsMinOverBorel L (gnImg T T ⊓ L) P)
    (hRP : gnImg T T ⊓ Subgroup.normalizer (L : Set (X ⧸ gnC T)) ≤
      Subgroup.normalizer (P : Set (X ⧸ gnC T)))
    {H₁ : Subgroup X} (hTH : T ≤ H₁)
    (hmap : gnImg T H₁ = conjClosure (pElementSubgroup 2 (conjClosure P
        (gnImg T T ⊓ Subgroup.normalizer (L : Set (X ⧸ gnC T))))) (gnImg T T) ⊔ gnImg T T)
    (hV : IsElemAbelian 2 (VZ T H₁)) (hnat : NatCaseGen H₁ T (VZ T H₁) hV) :
    baum T ≤ gnStab T (Subgroup.normalizer (L : Set (X ⧸ gnC T)) ⊓
      Subgroup.normalizer (P : Set (X ⧸ gnC T))) := by
  intro b hb
  obtain ⟨hbT, hbL⟩ := mem_gnStab.1 (baum_le_gnStab_of_natCase hX hL hPb hTH hmap hV hnat hb)
  exact mem_gnStab.2 ⟨hbT, hbL, hRP ⟨⟨b, hbT, rfl⟩, hbL⟩⟩

@[expose] def NatMultiBaumStabGraph : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T →
    ∀ L : Subgroup (X ⧸ gnC T), Open.IsComponentOf L ⊤ →
    IsChevTwo (↥L ⧸ Subgroup.center ↥L) →
    ∀ P : Subgroup (X ⧸ gnC T), IsMinOverBorel L (gnImg T T ⊓ L) P →
    ¬ gnImg T T ⊓ Subgroup.normalizer (L : Set (X ⧸ gnC T)) ≤
      Subgroup.normalizer (P : Set (X ⧸ gnC T)) →
    ∀ H₁ M₁ : Subgroup X, T ≤ H₁ →
      gnImg T H₁ = conjClosure (pElementSubgroup 2 (conjClosure P
        (gnImg T T ⊓ Subgroup.normalizer (L : Set (X ⧸ gnC T))))) (gnImg T T) ⊔ gnImg T T →
      MinParabolic H₁ T M₁ → CharTwo H₁ →
      ¬ thompsonJ T ≤ Subgroup.centralizer (VZ T H₁ : Set X) →
      ∀ hV : IsElemAbelian 2 (VZ T H₁), NatCaseGen H₁ T (VZ T H₁) hV →
      (∀ I, E23FamGen H₁ T (VZ T H₁) hV I →
          (∀ L ∈ I, ∃ n : ℕ, 2 ≤ n ∧ CFSG.Quasithin.E2.IsL2Natural L
            (fixV (autI hV (twoResidual H₁))) n) → 2 ≤ I.card) →
      baum T ≤ gnStab T (Subgroup.normalizer (L : Set (X ⧸ gnC T))) →
        baum T ≤ gnStab T (Subgroup.normalizer (L : Set (X ⧸ gnC T)) ⊓
          Subgroup.normalizer (P : Set (X ⧸ gnC T)))

theorem natMultiBaumStab_of_graph (h : NatMultiBaumStabGraph) : NatMultiBaumStab := by
  intro X _ _ T hX L hL hch P hPb H₁ M₁ hTH hmap hmin hF hJ hV hnat hall
  by_cases hRP : gnImg T T ⊓ Subgroup.normalizer (L : Set (X ⧸ gnC T)) ≤
      Subgroup.normalizer (P : Set (X ⧸ gnC T))
  · exact baum_le_gnStab_of_le_normalizer hX hL hPb hRP hTH hmap hV hnat
  · exact h X T hX L hL hch P hPb hRP H₁ M₁ hTH hmap hmin hF hJ hV hnat hall
      (baum_le_gnStab_of_natCase hX hL hPb hTH hmap hV hnat)

end CFSG.AGLEmbeddingD2.Tits.GN516
