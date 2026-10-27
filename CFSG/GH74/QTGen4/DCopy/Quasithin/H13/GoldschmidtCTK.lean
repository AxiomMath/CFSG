module

public import CFSG.Quasithin.H13.GoldschmidtCTK
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1515

public section

namespace CFSG.Quasithin.H13.A6

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.CTK
open scoped commutatorElement Pointwise

theorem Setting4.KH_le_fixV_F4 (S : Setting4 G T L V)
    (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
    {H : Subgroup G} (hH : H ∈ S.Hz) (hn : H ≤ Subgroup.normalizer (S.L1 : Set G))
    (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)) {l : ↥(Subgroup.normalizer (V : Set G))}
    {ω : Fin 6} (hω : ω = 4 ∨ ω = 5) (hl : S.frame.ρ l ω = ω) : S.KH H l ≤ S.fixV ω := by
  obtain ⟨hK4, -⟩ := S.lemma13_5_14_two_F4 hNS h1356two h13315 hH
    (S.UH_le_L1_six_F4 hNS h13315 h1356two hH hn hna) hna
  have hK4' : ∀ τ ∈ K4L, τ ω = ω := by
    rcases hω with rfl | rfl <;> decide +kernel
  refine sup_le (fun u hu => S.mem_fixV.2 ⟨_, hK4' _ (hK4 u hu)⟩) ?_
  rintro _ ⟨u, hu, rfl⟩
  have hu' := hK4 u hu
  have huN : u ∈ Subgroup.normalizer (V : Set G) :=
    S.frame.L_le (S.L1_le.trans inf_le_left (S.UH_le_L1_six_F4 hNS h13315 h1356two hH hn hna hu))
  have hmem : (l : G)⁻¹ * u * l ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ l.2) huN) l.2
  show (MulAut.conj (l : G)⁻¹) u ∈ S.fixV ω
  rw [MulAut.conj_apply, inv_inv]
  refine S.mem_fixV.2 ⟨hmem, ?_⟩
  have e : (⟨(l : G)⁻¹ * u * l, hmem⟩ : ↥(Subgroup.normalizer (V : Set G))) =
      l⁻¹ * ⟨u, huN⟩ * l := rfl
  rw [e, map_mul, map_mul, map_inv, Perm.mul_apply, Perm.mul_apply, hl,
    hK4' _ hu']
  exact Perm.inv_eq_iff_eq.2 hl.symm

theorem input13515CTK_of_F4 (h13315 : Stmt13_3_15_F4)
    (h1356two : Input1356Two_F4) (hobl : Obl13_5_14Six_F4) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat)
    (h36 : Vol2Native.A36CoreForSQTKCat) (hl2 : L2MultiplierFact)
    (hlist : ∀ (X : Type) [Group X] [Finite X], CFSG.SectionRank.IsSQTKCat X →
      ∀ (H : Subgroup X) (N : Subgroup ↥H) [N.Normal] [IsSimpleGroup (↥H ⧸ N)],
        (∃ a b : ↥H ⧸ N, a * b ≠ b * a) → CFSG.Milestones.SQTKSimpleList (↥H ⧸ N))
    (hExcl : ExclA5Block) : Input13515CTK_F4 := by
  intro G _ _ T L V S H l hNS hH hn hna hhat hl hlL hlT hρ
  have hsimple := S.h13.simple
  have hLS : LocalSQTK G := (qtkeCore_of_cat S.h13.nonabelian S.h13.qtke).1
  obtain ⟨hKeq, hshort, halt, hO2, hU, hQ8⟩ :=
    hobl G T L V S H l hNS hH hn hna hhat hl hlL hlT hρ
  obtain ⟨P⟩ : Nonempty (A5SitPf15 (S.toA5Sit_F4 hNS h13315 h1356two hH hna)
      (S.toA5SitY_F4 hNS h13315 h1356two hH hna hhat)) :=
    (S.toA5Sit_F4 hNS h13315 h1356two hH hna).nonempty_pf15 VolI.stmtF956i _ hn hU hQ8
  have hcTL : T ⊓ Subgroup.centralizer (L : Set G) = ⊥ :=
    P.centralizer_T_L S.uniqueM S.V_le_pCoreOf_M
  obtain ⟨y, hyI, hy3, hyN⟩ := P.S3_facts.2.2.2
  have hUH : conjClosure S.V3 H ≤ S.L5 :=
    (S.UH_le_L1_six_F4 hNS h13315 h1356two hH hn hna).trans S.L1_le_L5
  have hyD : ∀ d ∈ S.CD, y * d * y⁻¹ = d := fun d hd =>
    P.commute_y hyI hy3 hd.1 fun u hu =>
      (Subgroup.mem_centralizer_iff.mp hd.2 u (hUH hu)).symm
  have hmain : IsShort2 S.L5 → IsAltType S.L5 5 → pCoreOf 2 S.L5 = V → S.CD = ⊥ :=
    fun hs ha ho => (CTKHyp.mk hhat hs ha ho hcTL).CD_eq_bot hLS h37 h38 h39 h36 hl2 hlist
      hExcl ⟨y, hy3, hyN, hyD⟩
  have hKL : S.KH H l ≤ L := S.KH_le_L_F4 hNS h13315 h1356two hH hn hna (l := ⟨l, hl⟩) hlL
  have hKeq : oTwoRes (pCoreOf 2 (L ⊔ T) ⊔ S.KH H l) = S.KH H l := hKeq
  have hshort : IsShort2 (S.KH H l) := hshort
  have halt : IsAltType (S.KH H l) 5 := halt
  have hO2 : pCoreOf 2 (S.KH H l) = V := hO2
  show T ⊓ Subgroup.centralizer (S.KH H l : Set G) = ⊥
  rcases hρ with h4 | h5
  ·
    obtain ⟨t, htT, hρt⟩ :=
      S.frame.DA_T _ s0145_facts.1 (Perm.mem_alternatingGroup.2 s0145_facts.2.1)
    have htNV : (t : G) ∈ Subgroup.normalizer (V : Set G) := t.2
    have htL : (t : G) ∈ Subgroup.normalizer (L : Set G) := S.T_le_NL htT
    have hK4 : S.KH H l ≤ S.fixV 4 :=
      S.KH_le_fixV_F4 hNS h13315 h1356two hH hn hna (l := ⟨l, hl⟩) (ω := 4) (Or.inl rfl) h4
    have hQ : (t : G) ∈ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) :=
      le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_right htT)
    set K' : Subgroup G := (S.KH H l).map (MulAut.conj (t : G)).toMonoidHom with hK'
    have hK'fix : K' ≤ L ⊓ S.fix5V := by
      rintro _ ⟨k, hk, rfl⟩
      refine ⟨?_, S.mem_fix5V.2 ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp htL k).mp (hKL hk)
      · obtain ⟨hkN, hk4⟩ := S.mem_fixV.1 (hK4 hk)
        have hmem : (t : G) * k * (t : G)⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
          Subgroup.mul_mem _ (Subgroup.mul_mem _ htNV hkN) (Subgroup.inv_mem _ htNV)
        refine ⟨hmem, ?_⟩
        have e : (⟨(t : G) * k * (t : G)⁻¹, hmem⟩ : ↥(Subgroup.normalizer (V : Set G))) =
            t * ⟨k, hkN⟩ * t⁻¹ := rfl
        obtain ⟨hs4, hs5⟩ := s0145_apply
        show (S.frame.ρ ⟨(t : G) * k * (t : G)⁻¹, hmem⟩) 5 = 5
        rw [e, map_mul, map_mul, map_inv, hρt, Perm.mul_apply, Perm.mul_apply, hs5, hk4, hs4]
    have hshort' : IsShort2 K' := (Lin2.isShort2_map_equiv_iff (MulAut.conj (t : G)) _).2 hshort
    have halt' : IsAltType K' 5 := L238.IsAltType.map_equiv halt (MulAut.conj (t : G))
    have hO2' : pCoreOf 2 K' = V := by
      rw [hK', pCoreOf_map_equiv 2 (MulAut.conj (t : G)), hO2]
      exact CTK.map_conj_eq_of_mem_normalizer htNV
    have hKeq' : oTwoRes (pCoreOf 2 (L ⊔ T) ⊔ K') = K' := by
      have hmapQ : (pCoreOf 2 (L ⊔ T)).map (MulAut.conj (t : G)).toMonoidHom =
          pCoreOf 2 (L ⊔ T) := CTK.map_conj_eq_of_mem_normalizer hQ
      have h1 : conjSub (t : G) (pCoreOf 2 (L ⊔ T) ⊔ S.KH H l) =
          pCoreOf 2 (L ⊔ T) ⊔ K' := by
        show (pCoreOf 2 (L ⊔ T) ⊔ S.KH H l).map (MulAut.conj (t : G)).toMonoidHom = _
        rw [Subgroup.map_sup, hmapQ]
      rw [← h1, ← conjSub_oTwoRes, hKeq]
      rfl
    have hK'5 : K' = S.L5 := S.eq_L5 hhat hK'fix hshort' halt' hO2' hKeq'
    have hCD := hmain (hK'5 ▸ hshort') (hK'5 ▸ halt') (hK'5 ▸ hO2')
    refine eq_bot_iff.2 fun x hx => ?_
    have hxT : x ∈ T := hx.1
    have hz : (t : G) * x * (t : G)⁻¹ ∈ S.CD := by
      refine ⟨T.mul_mem (T.mul_mem htT hxT) (T.inv_mem htT), Subgroup.mem_centralizer_iff.2 ?_⟩
      intro k' hk'
      rw [← hK'5] at hk'
      obtain ⟨k, hk, rfl⟩ := hk'
      have hxk : k * x = x * k := Subgroup.mem_centralizer_iff.mp hx.2 k hk
      show (t : G) * k * (t : G)⁻¹ * ((t : G) * x * (t : G)⁻¹) =
        (t : G) * x * (t : G)⁻¹ * ((t : G) * k * (t : G)⁻¹)
      calc (t : G) * k * (t : G)⁻¹ * ((t : G) * x * (t : G)⁻¹)
          = (t : G) * (k * x) * (t : G)⁻¹ := by group
        _ = (t : G) * (x * k) * (t : G)⁻¹ := by rw [hxk]
        _ = (t : G) * x * (t : G)⁻¹ * ((t : G) * k * (t : G)⁻¹) := by group
    rw [hCD, Subgroup.mem_bot] at hz
    have : x = 1 := by
      have h2 : (t : G)⁻¹ * ((t : G) * x * (t : G)⁻¹) * (t : G) = x := by group
      rw [hz] at h2
      simpa using h2.symm
    exact (Subgroup.mem_bot).2 this
  · have hK5 : S.KH H l ≤ L ⊓ S.fix5V :=
      le_inf hKL ((S.KH_le_fixV_F4 hNS h13315 h1356two hH hn hna (l := ⟨l, hl⟩) (ω := 5)
        (Or.inr rfl) h5).trans S.fixV_five_le)
    have hK5eq : S.KH H l = S.L5 := S.eq_L5 hhat hK5 hshort halt hO2 hKeq
    rw [hK5eq]
    exact hmain (hK5eq ▸ hshort) (hK5eq ▸ halt) (hK5eq ▸ hO2)

end CFSG.Quasithin.H13.A6
