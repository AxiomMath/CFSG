module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsGF2
public import CFSG.CGT.PushingUpLit.BHS.TwoSixteenAlt
public import CFSG.Quasithin.Background.B6Offenders
public import CFSG.GroupTheory.TwoGroupFixedPoint
public import CFSG.CGT.PushingUpLit.Glue.NaturalIrred
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42Transport

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.CGT.PushingUpLit.BHS
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsAlt)
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

theorem isQuasisimple_of_isAlt {X : Type} [Group X] {n : ℕ} (h5 : 5 ≤ n) (hX : IsAlt X n) :
    CFSG.IsQuasisimple X := by
  obtain ⟨e⟩ := hX
  have hAn : CFSG.Open.IsQuasisimple (alternatingGroup (Fin n)) :=
    isQuasisimple_alternatingGroup h5
  have hXopen : CFSG.Open.IsQuasisimple X := isQuasisimple_of_mulEquiv' e.symm hAn
  exact (CFSG.Quasithin.A3.isQuasisimple_iff_open (Q := X)).mpr hXopen

omit [Finite W] in
private theorem altDn_pi_injective {n : ℕ} (h5 : 5 ≤ n) {H : Subgroup (MulAut W)}
    {π : (FFModel.altDn n).Gam →* ↥H} (hπs : Function.Surjective π) (hH : H ≠ ⊥) :
    Function.Injective π := by
  have : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simpa using h5)
  have : IsSimpleGroup (FFModel.altDn n).Gam := this
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h1 | h1
  · exact h1
  · exfalso
    apply hH
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨γ, hγ⟩ := hπs ⟨x, hx⟩
    have h2 : γ ∈ π.ker := by rw [h1]; exact Subgroup.mem_top γ
    rw [MonoidHom.mem_ker] at h2
    rw [Subgroup.mem_bot]
    have hγ' : ((π γ : ↥H) : MulAut W) = x := congrArg Subtype.val hγ
    have h2' : ((π γ : ↥H) : MulAut W) = 1 := congrArg Subtype.val h2
    rw [← hγ']
    exact h2'

private def altDnQuotEquiv {n : ℕ} (hn : Odd n) :
    (↥(FFModel.altDn n).sec ⧸
      (FFModel.altDn n).ker.subgroupOf (FFModel.altDn n).sec) ≃* ↥(FFModel.altDn n).sec :=
  (QuotientGroup.quotientMulEquivOfEq
    (CFSG.QuasithinUnique.L246.altDn_ker_subgroupOf_eq_bot hn)).trans
    QuotientGroup.quotientBot

private theorem altDnQuotEquiv_mk {n : ℕ} (hn : Odd n) (m : ↥(FFModel.altDn n).sec) :
    altDnQuotEquiv hn (QuotientGroup.mk m) = m := rfl

private theorem altDnQuotEquiv_mk_apply {n : ℕ} (hn : Odd n)
    (q : ↥(FFModel.altDn n).sec ⧸
      (FFModel.altDn n).ker.subgroupOf (FFModel.altDn n).sec) :
    QuotientGroup.mk (altDnQuotEquiv hn q) = q := by
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
  exact congrArg QuotientGroup.mk (altDnQuotEquiv_mk hn m)

omit [Finite W] in
theorem altDn_realizes_data {H : Subgroup (MulAut W)} {U Z : Subgroup W} {n : ℕ}
    (hn : Odd n) (h5 : 5 ≤ n) (hH : H ≠ ⊥) (h : (FFModel.altDn n).Realizes H U Z) :
    ∃ (θ : ↥H ≃* (FFModel.altDn n).Gam) (β : ↥U →* ↥(FFModel.altDn n).sec),
      Function.Surjective β ∧ β.ker = Z.subgroupOf U ∧
        ∀ (x : ↥H) (u : ↥U) (hu : (x : MulAut W) (u : W) ∈ U),
          β ⟨(x : MulAut W) (u : W), hu⟩ = (FFModel.altDn n).act (θ x) (β u) := by
  classical
  obtain ⟨π, hπs, hZU, hker_sec, hUinv, hZinv, hsec, hker, β₀, hβs, hβk, hβe⟩ := h
  have hπinj : Function.Injective π := altDn_pi_injective h5 hπs hH
  let πe : (FFModel.altDn n).Gam ≃* ↥H := MulEquiv.ofBijective π ⟨hπinj, hπs⟩
  let θ : ↥H ≃* (FFModel.altDn n).Gam := πe.symm
  have hθπ : ∀ e : ↥H, π (θ e) = e := fun e => MulEquiv.apply_symm_apply πe e
  let ρ := altDnQuotEquiv hn
  let β : ↥U →* ↥(FFModel.altDn n).sec := ρ.toMonoidHom.comp β₀
  have hβs' : Function.Surjective β := by
    intro x
    obtain ⟨u, hu⟩ := hβs (ρ.symm x)
    refine ⟨u, ?_⟩
    show ρ (β₀ u) = x
    rw [hu]
    exact ρ.apply_symm_apply x
  have hβk' : β.ker = Z.subgroupOf U := by
    ext u
    show ρ (β₀ u) = 1 ↔ u ∈ Z.subgroupOf U
    rw [← map_one ρ, ρ.injective.eq_iff, Subgroup.mem_subgroupOf]
    exact hβk u
  refine ⟨θ, β, hβs', hβk', ?_⟩
  intro x u hu
  have hπθ : ((π (θ x) : ↥H) : MulAut W) = (x : MulAut W) :=
    congrArg Subtype.val (hθπ x)
  have hu' : ((π (θ x) : ↥H) : MulAut W) (u : W) ∈ U := by
    rw [hπθ]
    exact hUinv x u u.2
  have hbound : β₀ u = QuotientGroup.mk (β u) := (altDnQuotEquiv_mk_apply hn (β₀ u)).symm
  have hm : (FFModel.altDn n).act (θ x) (β u) ∈ (FFModel.altDn n).sec :=
    hsec (θ x) (β u) (β u).2
  have hkey := hβe (θ x) u (β u) hu' hm hbound
  have harg : (⟨((π (θ x) : ↥H) : MulAut W) (u : W), hu'⟩ : ↥U) =
      ⟨(x : MulAut W) (u : W), hu⟩ := by
    apply Subtype.ext
    exact congrArg (fun g : MulAut W => g (u : W)) hπθ
  rw [← harg]
  show ρ (β₀ _) = (FFModel.altDn n).act (θ x) (β u)
  rw [hkey, altDnQuotEquiv_mk hn]

private def altDnGamEquiv (n : ℕ) :
    (FFModel.altDn n).Gam ≃* alternatingGroup (Fin n) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private def altDnSecEquiv (n : ℕ) : ↥(FFModel.altDn n).sec ≃* G6.coreMod n where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private theorem altDnSecEquiv_act (n : ℕ) (σ : (FFModel.altDn n).Gam)
    (x : ↥(FFModel.altDn n).sec)
    (hx : (FFModel.altDn n).act σ ((x : (FFModel.altDn n).sec) : (FFModel.altDn n).Amb) ∈
      (FFModel.altDn n).sec) :
    altDnSecEquiv n
        ⟨(FFModel.altDn n).act σ ((x : (FFModel.altDn n).sec) : (FFModel.altDn n).Amb), hx⟩ =
      G6.coreAct n ((altDnGamEquiv n σ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n))
        (altDnSecEquiv n x) := rfl

private theorem alt_coreMod_eq_bot_or_top_of_add {n : ℕ}
    {J : Subgroup (G6.coreMod n)} {N : AddSubgroup (Fin n → ZMod 2)}
    (hN : N = Subgroup.toAddSubgroup' (J.map (G6.coreMod n).subtype))
    (h : N = ⊥ ∨ N = CFSG.CGT.PushingUpLit.Glue.evenWeight n) : J = ⊥ ∨ J = ⊤ := by
  have htopmap : Subgroup.toAddSubgroup' (G6.coreMod n) =
      CFSG.CGT.PushingUpLit.Glue.evenWeight n := by
    ext x
    simp [Subgroup.mem_toAddSubgroup', G6.mem_coreMod,
      CFSG.CGT.PushingUpLit.Glue.mem_evenWeight_iff]
  rcases h with hbot | htop
  · left
    have hmap : J.map (G6.coreMod n).subtype = ⊥ := by
      apply Subgroup.toAddSubgroup'.injective
      rw [← hN, hbot]
      simp
    apply Subgroup.map_injective (G6.coreMod n).subtype_injective
    rw [hmap, Subgroup.map_bot]
  · right
    have hmap : J.map (G6.coreMod n).subtype = G6.coreMod n := by
      apply Subgroup.toAddSubgroup'.injective
      rw [← hN, htop, htopmap]
    apply Subgroup.map_injective (G6.coreMod n).subtype_injective
    rw [hmap, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

private theorem alt_coreMod_dichotomy {n : ℕ} (hn : Odd n) (h5 : 5 ≤ n)
    {J : Subgroup (G6.coreMod n)}
    (hJ : ∀ (σ : Equiv.Perm (Fin n)), σ ∈ alternatingGroup (Fin n) → ∀ j ∈ J,
      G6.coreAct n σ j ∈ J) : J = ⊥ ∨ J = ⊤ := by
  classical
  set N : AddSubgroup (Fin n → ZMod 2) :=
    Subgroup.toAddSubgroup' (J.map (G6.coreMod n).subtype) with hN
  have hNle : N ≤ CFSG.CGT.PushingUpLit.Glue.evenWeight n := by
    intro x hx
    rw [CFSG.CGT.PushingUpLit.Glue.mem_evenWeight_iff]
    have hx' : Multiplicative.ofAdd x ∈ J.map (G6.coreMod n).subtype := by
      simpa [N] using hx
    obtain ⟨j, -, hj⟩ := Subgroup.mem_map.mp hx'
    have hxeq : Multiplicative.toAdd (j : G6.PermMod n) = x := by
      change Multiplicative.toAdd ((coreMod n).subtype j) = x
      rw [hj]
      rfl
    rw [← hxeq]
    exact G6.mem_coreMod.mp j.2
  have hNinv : ∀ σ ∈ alternatingGroup (Fin n), ∀ x ∈ N,
      CFSG.CGT.PushingUpLit.Glue.permVec σ x ∈ N := by
    intro σ hσ x hx
    have hx' : Multiplicative.ofAdd x ∈ J.map (G6.coreMod n).subtype := by
      simpa [N] using hx
    obtain ⟨j, hjJ, hj⟩ := Subgroup.mem_map.mp hx'
    have hJj : G6.coreAct n σ j ∈ J := hJ σ hσ j hjJ
    have hmem : Multiplicative.ofAdd (CFSG.CGT.PushingUpLit.Glue.permVec σ x) ∈
        J.map (G6.coreMod n).subtype := by
      refine Subgroup.mem_map.mpr ⟨G6.coreAct n σ j, hJj, ?_⟩
      change (G6.coreAct n σ j : G6.PermMod n) =
        Multiplicative.ofAdd (CFSG.CGT.PushingUpLit.Glue.permVec σ x)
      rw [G6.coreAct_coe, show (j : G6.PermMod n) = Multiplicative.ofAdd x from hj]
      rfl
    simpa [N] using hmem
  exact alt_coreMod_eq_bot_or_top_of_add hN
    (CFSG.CGT.PushingUpLit.Glue.altInvariant_eq_bot_or_evenWeight hn (by omega) N hNle hNinv)

private theorem coreMod_nontrivial {n : ℕ} (h5 : 5 ≤ n) : Nontrivial (G6.coreMod n) := by
  have : NeZero n := ⟨by omega⟩
  let v : Fin n → ZMod 2 := CFSG.CGT.PushingUpLit.Glue.pairVec 0 1
  have hv : v ∈ CFSG.CGT.PushingUpLit.Glue.evenWeight n :=
    CFSG.CGT.PushingUpLit.Glue.pairVec_mem_evenWeight 0 1
  have hw : Multiplicative.ofAdd v ∈ G6.coreMod n := by
    rw [G6.mem_coreMod]
    simpa [v] using (CFSG.CGT.PushingUpLit.Glue.mem_evenWeight_iff v).mp hv
  have hwne : (Multiplicative.ofAdd v : G6.PermMod n) ≠ 1 := by
    intro h
    have h0 : v 0 = 0 := by
      have := congrArg (fun x : G6.PermMod n => Multiplicative.toAdd x 0) h
      simpa using this
    have h01 : (0 : Fin n) ≠ 1 := by
      intro h
      have hv1 : ((1 : Fin n) : ℕ) = 1 % n := Fin.val_one' n
      have hmod : (1 : ℕ) % n = 1 := Nat.mod_eq_of_lt (by omega)
      have := congrArg Fin.val h
      simp only [Fin.val_zero, hv1, hmod] at this
      omega
    have h1 : v 0 = 1 := by
      simp [v, CFSG.CGT.PushingUpLit.Glue.pairVec, h01]
    rw [h1] at h0
    exact one_ne_zero h0
  exact ⟨⟨Multiplicative.ofAdd v, hw⟩, 1, fun h => hwne (Subtype.ext_iff.mp h)⟩

omit [Finite W] in
private theorem altDn_realizes_coreData {H : Subgroup (MulAut W)} {U C : Subgroup W} {n : ℕ}
    (hn : Odd n) (h5 : 5 ≤ n) (hH : H ≠ ⊥) (h : (FFModel.altDn n).Realizes H U C) :
    ∃ (θ : ↥H ≃* alternatingGroup (Fin n)) (β : ↥U →* G6.coreMod n),
      Function.Surjective β ∧ β.ker = C.subgroupOf U ∧
        ∀ (x : ↥H) (u : ↥U) (hu : (x : MulAut W) (u : W) ∈ U),
          β ⟨(x : MulAut W) (u : W), hu⟩ = G6.coreAct n (θ x) (β u) := by
  obtain ⟨θD, βD, hβs, hβk, hβe⟩ := altDn_realizes_data hn h5 hH h
  let θ : ↥H ≃* alternatingGroup (Fin n) := θD.trans (altDnGamEquiv n)
  let β : ↥U →* G6.coreMod n := (altDnSecEquiv n).toMonoidHom.comp βD
  have hβs' : Function.Surjective β := by
    intro y
    obtain ⟨u, hu⟩ := hβs ((altDnSecEquiv n).symm y)
    refine ⟨u, ?_⟩
    show altDnSecEquiv n (βD u) = y
    rw [hu]
    exact (altDnSecEquiv n).apply_symm_apply y
  have hβk' : β.ker = C.subgroupOf U := by
    ext u
    show altDnSecEquiv n (βD u) = 1 ↔ u ∈ C.subgroupOf U
    rw [← map_one (altDnSecEquiv n), (altDnSecEquiv n).injective.eq_iff, ← MonoidHom.mem_ker, hβk]
  refine ⟨θ, β, hβs', hβk', ?_⟩
  intro x u hu
  have h := hβe x u hu
  have hx : (FFModel.altDn n).act (θD x) (βD u) ∈ (FFModel.altDn n).sec :=
    h ▸ (βD ⟨(x : MulAut W) (u : W), hu⟩).2
  show altDnSecEquiv n (βD ⟨(x : MulAut W) (u : W), hu⟩) =
    G6.coreAct n (θ x) (altDnSecEquiv n (βD u))
  have hsub : βD ⟨(x : MulAut W) (u : W), hu⟩ =
      ⟨(FFModel.altDn n).act (θD x) (βD u), hx⟩ := Subtype.ext h
  rw [hsub]
  simpa [θ, MulEquiv.trans_apply] using altDnSecEquiv_act n (θD x) (βD u) hx

omit [Finite W] in
private theorem alt_realizes_ne_bot {H : Subgroup (MulAut W)} {U C : Subgroup W} {n : ℕ}
    (hn : Odd n) (h5 : 5 ≤ n) (hH : H ≠ ⊥) (h : (FFModel.altDn n).Realizes H U C) :
    C ≠ U := by
  obtain ⟨θ, β, hβs, hβk, hβe⟩ := altDn_realizes_coreData hn h5 hH h
  intro hCU
  have hker_top : β.ker = ⊤ := by
    rw [hβk, hCU, Subgroup.subgroupOf_self]
  have : Nontrivial (G6.coreMod n) := coreMod_nontrivial h5
  have hsub : Subsingleton (G6.coreMod n) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨u, rfl⟩ := hβs a
    obtain ⟨v, rfl⟩ := hβs b
    have hu : u ∈ β.ker := by rw [hker_top]; exact Subgroup.mem_top u
    have hv : v ∈ β.ker := by rw [hker_top]; exact Subgroup.mem_top v
    rw [MonoidHom.mem_ker] at hu hv
    rw [hu, hv]
  exact (not_subsingleton (G6.coreMod n)) hsub

omit [Finite W] in
private theorem alt_realizes_Jc_inv {H : Subgroup (MulAut W)} {U : Subgroup W} {n : ℕ}
    {θ : ↥H ≃* alternatingGroup (Fin n)} {β : ↥U →* G6.coreMod n}
    (hβe : ∀ (x : ↥H) (u : ↥U) (hu : (x : MulAut W) (u : W) ∈ U),
      β ⟨(x : MulAut W) (u : W), hu⟩ = G6.coreAct n (θ x) (β u))
    {J : Subgroup W} (hJU : J ≤ U) (hJinv : ∀ x ∈ H, ∀ w ∈ J, x w ∈ J) :
    ∀ σ ∈ alternatingGroup (Fin n), ∀ j ∈ (J.subgroupOf U).map β,
      G6.coreAct n σ j ∈ (J.subgroupOf U).map β := by
  intro σ hσ j hj
  obtain ⟨u, huJ', huβ⟩ := Subgroup.mem_map.mp hj
  obtain ⟨x, hx⟩ := θ.surjective ⟨σ, hσ⟩
  have huJ : (u : W) ∈ J := Subgroup.mem_subgroupOf.mp huJ'
  have hxU : (x : MulAut W) (u : W) ∈ U := hJU (hJinv x x.2 (u : W) huJ)
  have hmem : β ⟨(x : MulAut W) (u : W), hxU⟩ ∈ (J.subgroupOf U).map β :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (hJinv x x.2 (u : W) huJ))
  have hx' : (θ x : Equiv.Perm (Fin n)) = σ := congrArg Subtype.val hx
  have heq : G6.coreAct n σ (β u) = β ⟨(x : MulAut W) (u : W), hxU⟩ := by
    rw [← hx']
    exact (hβe x u hxU).symm
  rw [← huβ, heq]
  exact hmem

omit [Finite W] in
private theorem alt_realizes_dichotomy {H : Subgroup (MulAut W)} {U C : Subgroup W} {n : ℕ}
    (hn : Odd n) (h5 : 5 ≤ n) (hH : H ≠ ⊥)
    (h : (FFModel.altDn n).Realizes H U C)
    {J : Subgroup W} (hCJ : C ≤ J) (hJU : J ≤ U)
    (hJinv : ∀ x ∈ H, ∀ w ∈ J, x w ∈ J) : J = C ∨ J = U := by
  obtain ⟨θ, β, hβs, hβk, hβe⟩ := altDn_realizes_coreData hn h5 hH h
  set J' : Subgroup ↥U := J.subgroupOf U with hJ'
  have hJc_inv := alt_realizes_Jc_inv (J := J) hβe hJU hJinv
  set Jc : Subgroup (G6.coreMod n) := J'.map β with hJc
  have hJc_inv' : ∀ σ ∈ alternatingGroup (Fin n), ∀ j ∈ Jc, G6.coreAct n σ j ∈ Jc := hJc_inv
  rcases alt_coreMod_dichotomy hn h5 hJc_inv' with hJcbot | hJctop
  · left
    have hJ'le : J' ≤ β.ker := by
      intro u hu
      have hmem : β u ∈ Jc := Subgroup.mem_map_of_mem _ hu
      rw [hJcbot, Subgroup.mem_bot] at hmem
      exact MonoidHom.mem_ker.mpr hmem
    rw [hβk] at hJ'le
    refine le_antisymm ?_ hCJ
    intro w hw
    have hwU : w ∈ U := hJU hw
    have hw' : (⟨w, hwU⟩ : ↥U) ∈ J' := Subgroup.mem_subgroupOf.mpr hw
    exact Subgroup.mem_subgroupOf.mp (hJ'le hw')
  · right
    have hJ'top : J' = ⊤ := by
      refine le_antisymm le_top ?_
      intro u _
      have hmem : β u ∈ Jc := by rw [hJctop]; exact Subgroup.mem_top _
      obtain ⟨v, hvJ', hvβ⟩ := Subgroup.mem_map.mp hmem
      have hker : u * v⁻¹ ∈ β.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hvβ]
        exact mul_inv_cancel (β u)
      rw [hβk] at hker
      have hCJ' : u * v⁻¹ ∈ J' :=
        Subgroup.mem_subgroupOf.mpr (hCJ (Subgroup.mem_subgroupOf.mp hker))
      have hu : u = (u * v⁻¹) * v := by group
      rw [hu]
      exact J'.mul_mem hCJ' hvJ'
    refine le_antisymm hJU ?_
    intro w hw
    have hw' : (⟨w, hw⟩ : ↥U) ∈ J' := by
      rw [hJ'top]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hw'

omit [Finite W] in
private theorem ne_bot_of_isAlt {L : Subgroup (MulAut W)} {n : ℕ} (h3 : 3 ≤ n)
    (hL : IsAlt ↥L n) : L ≠ ⊥ := by
  obtain ⟨e⟩ := hL
  have : Nontrivial (alternatingGroup (Fin n)) :=
    alternatingGroup.nontrivial_of_three_le_card (by simpa using h3)
  have : Nontrivial ↥L := by
    obtain ⟨a, b, hab⟩ := exists_pair_ne (alternatingGroup (Fin n))
    exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective h)⟩
  exact (Subgroup.nontrivial_iff_ne_bot L).mp inferInstance

omit [Finite W] in
theorem commV_mem_irrPlus_of_altDn {L : Subgroup (MulAut W)} {n : ℕ} (hn : Odd n)
    (h5 : 5 ≤ n) (hL : IsAlt ↥L n)
    (hnat : (FFModel.altDn n).Realizes L (commV L) (gomiWXKer L)) :
    commV L ∈ IrrPlus L ⊤ := by
  rw [mem_irrPlus_top_iff]
  have hH : L ≠ ⊥ := ne_bot_of_isAlt (by omega) hL
  have hQ : CFSG.IsQuasisimple ↥L := isQuasisimple_of_isAlt h5 hL
  have hperf : ⁅L, L⁆ = L := by
    have htop : (⊤ : Subgroup ↥L).map L.subtype = L := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have h := Subgroup.map_commutator (H₁ := (⊤ : Subgroup ↥L)) (H₂ := ⊤) L.subtype
    rw [htop] at h
    rw [← h, ← commutator_def, Group.isPerfect_def.mp hQ.1, htop]
  have hinv : ∀ x ∈ L, ∀ w ∈ commV L, x w ∈ commV L := fun x hx w hw =>
    commV_apply_mem_of_mem_normalizer (Subgroup.le_normalizer hx) hw
  have hcomm : commSub (commV L) L = commV L := CFSG.Quasithin.B15P4.commSub_commV_of_perfect hperf
  have hCU : gomiWXKer L ≤ commV L := inf_le_left
  have hne : gomiWXKer L ≠ commV L := alt_realizes_ne_bot hn h5 hH hnat
  refine ⟨hinv, hcomm, lt_of_le_of_ne inf_le_left hne, ?_⟩
  intro J hJinv hCJ hJU
  exact alt_realizes_dichotomy hn h5 hH hnat hCJ hJU hJinv

omit [Finite W] in
private theorem alt_realizes_upper_ne_bot {H : Subgroup (MulAut W)} {U C : Subgroup W} {n : ℕ}
    (hn : Odd n) (h5 : 5 ≤ n) (hH : H ≠ ⊥) (h : (FFModel.altDn n).Realizes H U C) :
    U ≠ ⊥ := by
  obtain ⟨θ, β, hβs, hβk, hβe⟩ := altDn_realizes_coreData hn h5 hH h
  intro hUbot
  have : Nontrivial (G6.coreMod n) := coreMod_nontrivial h5
  have hsubU : Subsingleton ↥U := by rw [hUbot]; infer_instance
  have hsub : Subsingleton (G6.coreMod n) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨u, rfl⟩ := hβs a
    obtain ⟨v, rfl⟩ := hβs b
    rw [Subsingleton.elim u v]
  exact (not_subsingleton (G6.coreMod n)) hsub

private theorem altDn_inf_fixV_ffJ_ne_bot (hW : ∀ w : W, w ^ 2 = 1)
    {S L : Subgroup (MulAut W)} (hS : IsPGroup 2 ↥S) {n : ℕ} (hn : Odd n) (h5 : 5 ≤ n)
    (hH : L ≠ ⊥) (hnat : (FFModel.altDn n).Realizes L (commV L) (gomiWXKer L))
    (hN : ffJ S ≤ Subgroup.normalizer (L : Set (MulAut W))) :
    commV L ⊓ fixV (ffJ S) ≠ ⊥ := by
  have hU2 : IsPGroup 2 ↥(commV L) := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro u
    exact ⟨1, by rw [pow_one]; exact Subtype.ext (hW (u : W))⟩
  have hT2 : IsPGroup 2 ↥(ffJ S) := hS.to_le (CFSG.Quasithin.B6.ffJ_le S)
  have hUne : commV L ≠ ⊥ := alt_realizes_upper_ne_bot hn h5 hH hnat
  have : Nontrivial ↥(commV L) := (Subgroup.nontrivial_iff_ne_bot _).mpr hUne
  have hInv : CFSG.IsInvariant ↥(ffJ S) W (commV L) :=
    ⟨fun a g => by
      constructor
      · intro hg
        exact commV_apply_mem_of_mem_normalizer (hN a.2) hg
      · intro hg
        have h := commV_apply_mem_of_mem_normalizer (hN (Subgroup.inv_mem _ a.2)) hg
        have h1 : ((a : MulAut W)⁻¹) (a • g) = g := by
          rw [Subgroup.smul_def, MulAut.smul_def]
          exact MulEquiv.symm_apply_apply (a : MulAut W) g
        rwa [h1] at h⟩
  let : MulDistribMulAction ↥(ffJ S) ↥(commV L) := CFSG.instMulDistribMulAction_subtype
  obtain ⟨v, hvne, hvfix⟩ :=
    CFSG.exists_nontrivial_fixed_point_of_isPGroup_two hT2 hU2 inferInstance
  intro hbot
  have hvmem : (v : W) ∈ commV L ⊓ fixV (ffJ S) := by
    refine ⟨v.2, mem_fixV.mpr fun g hg => ?_⟩
    have hfix' : (⟨g, hg⟩ : ↥(ffJ S)) • v = v := hvfix ⟨g, hg⟩
    have h2 : ((⟨g, hg⟩ : ↥(ffJ S)) • v : W) = (v : W) :=
      congrArg (fun x : ↥(commV L) => (x : W)) hfix'
    change ((⟨g, hg⟩ : ↥(ffJ S)) : MulAut W) (v : W) = (v : W) at h2
    exact h2
  have hv1 : (v : W) = 1 := Subgroup.mem_bot.mp (hbot ▸ hvmem)
  exact hvne (Subtype.ext hv1)

theorem not_inf_fixV_ffJ_le_of_altDn (hW : ∀ w : W, w ^ 2 = 1)
    {S L : Subgroup (MulAut W)} (hS : IsPGroup 2 ↥S) {n : ℕ} (hn : Odd n) (h5 : 5 ≤ n)
    (hL : IsAlt ↥L n) (hnat : (FFModel.altDn n).Realizes L (commV L) (gomiWXKer L))
    (hN : ffJ S ≤ Subgroup.normalizer (L : Set (MulAut W)))
    {A : Subgroup (MulAut W)} (hA : IsFFStarOffender S A) (hLA : ⁅L, A⁆ ≠ ⊥) :
    ¬ commV L ⊓ fixV (ffJ S) ≤ gomiWXKer L := by
  have hH : L ≠ ⊥ := ne_bot_of_isAlt (by omega) hL
  obtain ⟨θ, β, hβs, hβk, hβe⟩ := altDn_realizes_coreData hn h5 hH hnat
  have hAffJ : A ≤ ffJ S := CFSG.Quasithin.B6.le_ffJ hA
  have hAN : A ≤ Subgroup.normalizer (L : Set (MulAut W)) := hAffJ.trans hN
  have hAoff : IsOff A := (offender_iff.mp hA).2
  have hWker : gomiWXKer L = ⊥ :=
    (two_sixteen_alt_gen hW hn h5 (A := A) (E := L) (W := commV L) rfl θ β hβs hβk
      hβe hAN hAoff hLA).1
  have hfix := altDn_inf_fixV_ffJ_ne_bot hW hS hn h5 hH hnat hN
  intro hle
  rw [hWker] at hle
  exact hfix (le_bot_iff.mp hle)
