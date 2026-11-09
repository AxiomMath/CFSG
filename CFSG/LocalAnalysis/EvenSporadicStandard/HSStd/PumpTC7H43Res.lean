module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1LMain
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnToral
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTC7H43Data
public import CFSG.RankThree.Native.PermEnumeration
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTC7Word
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTC7Class
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTC7Skel
public import CFSG.RankThree.PartOne.KS.OrbitCert

public section

namespace CFSG.EvenSporadicStandard.HSStd.PumpTC7

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
  CFSG.Sporadic.SmallOddCore CFSG.ComponentClassification.HarrisLit.P1.L43
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Sporadic.SmallOddCore.Native
  CFSG.Certificates.Native CFSG.ComponentClassification.HarrisLit.P1 CFSG.Monster.B.Fischer

theorem rhoPt_scalar (d : (ZMod 3)ˣ) : rho (Matrix.GeneralLinearGroup.scalar (Fin 4) d) = 1 := by
  ext i
  rw [rho_apply, Equiv.Perm.one_apply, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mulVec,
    Matrix.one_mulVec, ptIndex_smul d.ne_zero, ptIndex_decode]

theorem scalars_le_ker40 :
    scalars 4 (ZMod 3) ≤ (rho.comp Matrix.SpecialLinearGroup.toGL).ker := by
  rintro A ⟨c, -, hA⟩
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
  have h1 : Matrix.SpecialLinearGroup.toGL A = Matrix.GeneralLinearGroup.scalar (Fin 4) c := by
    apply Units.ext
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hA, Matrix.GeneralLinearGroup.coe_scalar]
  rw [h1, rhoPt_scalar]

@[expose] noncomputable def pi40 : projectiveSL 4 (ZMod 3) →* Equiv.Perm (Fin 40) :=
  QuotientGroup.lift _ (rho.comp Matrix.SpecialLinearGroup.toGL) scalars_le_ker40

theorem pi40_apply (g : projectiveSL 4 (ZMod 3)) (i : Fin 40) :
    (pi40 g i : ℕ) = (pi g (Fin.castAdd 40 i) : ℕ) := by
  obtain ⟨h, rfl⟩ := proj_surjective 4 (ZMod 3) g
  rw [pi_proj, perm80_apply_lt _ _ (by simp)]
  rfl

theorem rep_res40 {a : Array ℕ} {g : projectiveSL 4 (ZMod 3)} (h : Rep 80 a (pi g)) :
    Rep 40 (res40 a) (pi40 g) := fun x => by
  rw [res40, getElem!_ofFn_nat _ x.2, pi40_apply]
  exact h (Fin.castAdd 40 x)

theorem pi40_injective : Function.Injective pi40 := by
  have : IsSimpleGroup (projectiveSL 4 (ZMod 3)) :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.isSimpleGroup_projectiveSL (by norm_num)
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases (MonoidHom.normal_ker pi40).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have hx : pi40 xElt = 1 := (MonoidHom.mem_ker).1 (h ▸ mem_top xElt)
    have hmv : ((List.range 40).any fun i => (tab80 codeA false)[i]! != i) = true := by
      decide +kernel
    obtain ⟨i, hi, hne⟩ := List.any_eq_true.1 hmv
    have hi' : i < 40 := List.mem_range.1 hi
    have e1 := rep_res40 rep_tabA ⟨i, hi'⟩
    rw [hx, Equiv.Perm.one_apply, res40, getElem!_ofFn_nat _ hi'] at e1
    simp [e1] at hne

theorem card_range_pi40 : Nat.card pi40.range = 6065280 := by
  rw [← card_P]
  exact Nat.card_congr (MonoidHom.ofInjective pi40_injective).toEquiv.symm

theorem gs40_size : gs40.size = 2 := by simp [gs40, gsP, pgTbls]

theorem rep_gs40 : ∀ k < 2, Rep 40 gs40[k]! (pi40 (if k = 0 then xElt else yElt)) := by
  intro k hk
  have hk' : k < pgTbls.size := by simpa [pgTbls] using hk
  have h80 : Rep 80 gsP[k]! (l43Gens k) := by
    have e : gsP[k]! = natArr pgTbls[k]! := by
      change (pgTbls.map natArr)[k]! = natArr pgTbls[k]!
      rw [getElem!_pos (pgTbls.map natArr) k (by simpa using hk'), Array.getElem_map,
        getElem!_pos pgTbls k hk']
    rw [e]
    exact co2Rep_natArr_iff.2 (l43_groupData.rep k hk')
  have e40 : gs40[k]! = res40 gsP[k]! := by
    have hk2 : k < gsP.size := by simpa [gsP] using hk'
    rw [gs40, getElem!_pos (gsP.map res40) k (by simpa using hk2), Array.getElem_map,
      getElem!_pos gsP k hk2]
  rw [e40]
  refine rep_res40 ?_
  unfold l43Gens at h80
  split_ifs at h80 ⊢ <;> exact h80

theorem validA_gs40 : ∀ k < gs40.size, validA 40 gs40[k]! = true := fun k hk =>
  validA_of_rep (rep_gs40 k (gs40_size ▸ hk))

theorem closure_gs40 : Subgroup.closure (permsA 40 gs40) = pi40.range := by
  have hset : permsA 40 gs40 = {pi40 xElt, pi40 yElt} := by
    ext g
    simp only [permsA, Set.mem_image, Set.mem_ofPred_eq, gs40_size, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hk2 : k < 2 := hk
      rw [permOfArr_eq_of_rep (rep_gs40 k hk2)]
      interval_cases k <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, by norm_num, permOfArr_eq_of_rep (rep_gs40 0 (by norm_num))⟩
      · exact ⟨1, by norm_num, permOfArr_eq_of_rep (rep_gs40 1 (by norm_num))⟩
  rw [hset, MonoidHom.range_eq_map, ← closure_xy, MonoidHom.map_closure, Set.image_pair]

theorem card_range_inf_cent_inj {G H : Type*} [Group G] [Group H] {f : G →* H}
    (hf : Function.Injective f) (g : G) :
    Nat.card ↥(f.range ⊓ centralizer ({f g} : Set H)) =
      Nat.card ↥(centralizer ({g} : Set G)) := by
  have e : (centralizer ({g} : Set G)).map f = f.range ⊓ centralizer ({f g} : Set H) := by
    ext y
    simp only [mem_map, mem_inf, MonoidHom.mem_range, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, rfl⟩, by rw [← map_mul, ← map_mul, hx]⟩
    · rintro ⟨⟨x, rfl⟩, hx⟩
      refine ⟨x, hf ?_, rfl⟩
      rw [map_mul, map_mul]
      exact hx
  rw [← e, Subgroup.card_map_of_injective hf]

theorem keys43_lt40 : ∀ p ∈ keys43, p < 40 := by decide

theorem card_cent_of_class40 {x : Array ℕ} {cc : ArrCert}
    (hcc : arrCertOK (fun k a => conjA 40 gs40[k]! a) gs40.size (validA 40) (keyA 40 keys43) x
      cc = true)
    (hsize : cc.pts.size = 74880) {h : projectiveSL 4 (ZMod 3)} {m : ℕ} (hm : m < cc.pts.size)
    (hzm : permOfArr 40 cc.pts[m]! = pi40 h) :
    Nat.card ↥(pi.range ⊓ centralizer ({pi h} : Set (Equiv.Perm (Fin 80)))) = 81 := by
  obtain ⟨g, hg, hzg⟩ := (mem_class_iff validA_gs40 hcc (pi40 h)).2 ⟨m, hm, hzm⟩
  rw [closure_gs40] at hg
  have hos := (CFSG.RankThree.PartOne.card_closure_eq_card_mul_card_centralizer keys43_lt40
    validA_gs40 hcc).2
  rw [closure_gs40, card_range_pi40, hsize] at hos
  have hC : Nat.card ↥(pi40.range ⊓
      centralizer ({permOfArr 40 x} : Set (Equiv.Perm (Fin 40)))) = 81 := by
    omega
  rw [card_range_inf_cent_inj pi_injective h, ← card_range_inf_cent_inj pi40_injective h,
    hzg, card_inf_centralizer_conj hg, hC]

end CFSG.EvenSporadicStandard.HSStd.PumpTC7

end
