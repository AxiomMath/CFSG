module

public import CFSG.Holt.H78.Bridge
import CFSG.Holt.H78.AltModelSylow
public import CFSG.GroupTheory.ABGLocalTools.PStabilityDGroup

public section

namespace CFSG.Holt.H78

open MulAction
open scoped commutatorElement

private theorem pCore_pointStabilizer_ne_bot_of_isNaturalSE
    {Δ : Type*} [Fintype Δ] [DecidableEq Δ] {M : Subgroup (Equiv.Perm Δ)}
    (hM : IsNaturalSE M) (b : Δ) :
    pCore 2 ↥(MulAction.stabilizer M b) ≠ ⊥ := by
  classical
  obtain ⟨q, e, hB⟩ := hM
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hB.exists_sylow_le_stabilizer b
  let eTop : ↥(⊤ : Subgroup M) ≃* M := Subgroup.topEquiv
  let Q' : Subgroup M := (Q : Subgroup ↥(⊤ : Subgroup M)).map eTop.toMonoidHom
  have hQcard : Nat.card (Q : Subgroup ↥(⊤ : Subgroup M)) = q ^ e :=
    (hB.benderBorel Q).2.2.2.2
  have hQ'card : Nat.card Q' = q ^ e := by
    rw [show Q' = (Q : Subgroup ↥(⊤ : Subgroup M)).map eTop.toMonoidHom from rfl,
      Subgroup.card_map_of_injective eTop.injective, hQcard]
  have hq : 1 < q ^ e := by
    obtain ⟨hq, -, he, -⟩ := hB.params
    exact Nat.one_lt_pow (by omega) (by omega)
  have hQ'ne : Q' ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hQ'card
    omega
  have hQ'p : IsPGroup 2 Q' := (Q.isPGroup').map eTop.toMonoidHom
  have hQ'le : Q' ≤ MulAction.stabilizer M b := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine mem_stabilizer_iff.mpr ?_
    have hyfix : (y : ↥(⊤ : Subgroup M)) • b = b := hQ hy
    simpa [eTop, Subgroup.smul_def, Subgroup.topEquiv_apply] using hyfix
  have hstab_map : (MulAction.stabilizer ↥(⊤ : Subgroup M) b).map eTop.toMonoidHom =
      MulAction.stabilizer M b := by
    ext m
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [eTop, Subgroup.smul_def, Subgroup.topEquiv_apply] using hy
    · intro hm
      exact ⟨eTop.symm m,
        by simpa [eTop, Subgroup.smul_def, Subgroup.topEquiv_symm_apply_coe] using hm, by simp⟩
  have hstab_norm : MulAction.stabilizer M b = Subgroup.normalizer (Q' : Set M) := by
    calc MulAction.stabilizer M b
        = (MulAction.stabilizer ↥(⊤ : Subgroup M) b).map eTop.toMonoidHom := hstab_map.symm
      _ = (Subgroup.normalizer ((Q : Subgroup ↥(⊤ : Subgroup M)) : Set
            ↥(⊤ : Subgroup M))).map eTop.toMonoidHom := by
          rw [hB.stabilizer_eq_normalizer b Q hQ]
      _ = Subgroup.normalizer (Q' : Set M) := by
          rw [Subgroup.map_equiv_normalizer_eq]
  have hQ'norm : (Q'.subgroupOf (MulAction.stabilizer M b)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQ'le, hstab_norm]
  have hQ'sub_p : IsPGroup 2 (Q'.subgroupOf (MulAction.stabilizer M b)) :=
    hQ'p.comap_subtype (K := MulAction.stabilizer M b)
  intro hbot
  have hle : Q'.subgroupOf (MulAction.stabilizer M b) ≤
      pCore 2 ↥(MulAction.stabilizer M b) :=
    le_sSup ⟨hQ'norm, hQ'sub_p⟩
  rw [hbot] at hle
  have hsubbot : Q'.subgroupOf (MulAction.stabilizer M b) = ⊥ := le_bot_iff.mp hle
  have hcard : Nat.card (Q'.subgroupOf (MulAction.stabilizer M b)) = Nat.card Q' :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ'le).toEquiv
  have hsubcard : Nat.card (Q'.subgroupOf (MulAction.stabilizer M b)) = 1 :=
    (Subgroup.eq_bot_iff_card (H := Q'.subgroupOf (MulAction.stabilizer M b))).mp hsubbot
  have hQ'card1 : Nat.card Q' = 1 := by rw [← hcard, hsubcard]
  exact hQ'ne ((Subgroup.eq_bot_iff_card (H := Q')).mpr hQ'card1)

private theorem range_lEquiv_inf_stabilizer {G : Type*} [Group G] [Finite G]
    {Ω : Type*} [MulAction G Ω] [Finite Ω] {D : HoltData G Ω}
    (hO : jOddCore G Ω = ⊥) (i : D.ι) (α : Ω) :
    ((D.lEquiv hO i).toMonoidHom.comp
        (Subgroup.inclusion (inf_le_left : D.L i ⊓ MulAction.stabilizer G α ≤ D.L i))).range =
      MulAction.stabilizer (D.M i) (D.coord α i) := by
  classical
  ext m
  constructor
  · rintro ⟨k, rfl⟩
    refine mem_stabilizer_iff.mpr ?_
    have hkL : (k : G) ∈ D.L i := k.2.1
    have hkα : (k : G) • α = α := k.2.2
    have hc : D.ρ i ⟨(k : G), D.L_le i hkL⟩ (D.coord α i) = D.coord α i := by
      have h := D.coord_smul (⟨(k : G), D.L_le i hkL⟩ : jHull G Ω) α i
      rw [hkα] at h
      exact h.symm
    simpa [Subgroup.smul_def, Equiv.Perm.smul_def, D.rhoL_apply, D.coe_lEquiv_apply] using hc
  · intro hm
    have hmperm : (m : Equiv.Perm (D.Ψc i)) (D.coord α i) = D.coord α i := by
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using (mem_stabilizer_iff.mp hm)
    let l : D.L i := (D.lEquiv hO i).symm m
    have hlfix : (l : G) • α = α := by
      apply D.coord_injective hO
      funext j
      by_cases hji : j = i
      · subst j
        have hle : (D.lEquiv hO i l : Equiv.Perm (D.Ψc i)) = m := by simp [l]
        have h := D.coord_smul (⟨(l : G), D.L_le i l.2⟩ : jHull G Ω) α i
        rw [← D.coe_lEquiv_apply (hO := hO) i l, hle, hmperm] at h
        simpa using h
      · have h := D.coord_smul (⟨(l : G), D.L_le i l.2⟩ : jHull G Ω) α j
        rw [D.rho_eq_one_of_mem_L (i := i) (j := j) (fun h => hji h.symm) l.2,
          Equiv.Perm.one_apply] at h
        simpa using h
    refine ⟨⟨l, Subgroup.mem_inf.mpr ⟨l.2, hlfix⟩⟩, ?_⟩
    change (D.lEquiv hO i) l = m
    exact (D.lEquiv hO i).apply_symm_apply m

private noncomputable def stabilizerEquiv {G : Type*} [Group G] [Finite G]
    {Ω : Type*} [MulAction G Ω] [Finite Ω] {D : HoltData G Ω}
    (hO : jOddCore G Ω = ⊥) (i : D.ι) (α : Ω) :
    ↥(D.L i ⊓ MulAction.stabilizer G α) ≃*
      ↥(MulAction.stabilizer (D.M i) (D.coord α i)) :=
  (MonoidHom.ofInjective (by
    intro a b hab
    exact Subgroup.inclusion_injective inf_le_left ((D.lEquiv hO i).injective hab))).trans
    (MulEquiv.subgroupCongr (range_lEquiv_inf_stabilizer hO i α))

private theorem pCore_stabilizer_ne_bot_of_isNaturalSE {G : Type*} [Group G] [Finite G]
    {Ω : Type*} [MulAction G Ω] [Finite Ω] {D : HoltData G Ω}
    (hO : jOddCore G Ω = ⊥) (α : Ω) {i : D.ι} (hSE : IsNaturalSE (D.M i)) :
    pCore 2 ↥(MulAction.stabilizer G α) ≠ ⊥ := by
  classical
  let S : Subgroup G := MulAction.stabilizer G α
  let K : Subgroup G := D.L i ⊓ S
  let Hα : Subgroup G := jHull G Ω ⊓ S
  have hKleH : K ≤ Hα := inf_le_inf (D.L_le i) le_rfl
  have hKH : K ≤ Hα := hKleH
  have hKnorm : (K.subgroupOf Hα).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKleH]
    intro h hh
    refine Subgroup.inf_normalizer_le_normalizer_inf ⟨?_, ?_⟩
    · exact D.le_normalizer i hh.1
    · exact Subgroup.le_normalizer hh.2
  have hHleS : Hα ≤ S := inf_le_right
  have hHnorm : (Hα.subgroupOf S).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hHleS]
    intro s hs
    refine Subgroup.inf_normalizer_le_normalizer_inf ⟨?_, ?_⟩
    · exact Subgroup.le_normalizer_of_normal hs
    · exact Subgroup.le_normalizer hs
  have hTcore : pCore 2 ↥(MulAction.stabilizer (D.M i) (D.coord α i)) ≠ ⊥ :=
    pCore_pointStabilizer_ne_bot_of_isNaturalSE hSE _
  have hKcore : pCore 2 ↥K ≠ ⊥ := by
    intro hbot
    have hmap := pCore_map_iso 2 (stabilizerEquiv (D := D) hO i α)
    rw [hbot, Subgroup.map_bot] at hmap
    exact hTcore hmap.symm
  have hHcore : pCore 2 ↥Hα ≠ ⊥ := by
    intro hbot
    have hmap := CFSG.ABGLocalTools.map_pCore_le_of_injective_of_normal (p := 2)
      (Subgroup.inclusion hKH) (Subgroup.inclusion_injective hKH) (by
        rw [Subgroup.inclusion_range]
        exact hKnorm)
    rw [hbot] at hmap
    have hmapbot : (pCore 2 ↥K).map (Subgroup.inclusion hKH) = ⊥ := le_bot_iff.mp hmap
    exact hKcore ((Subgroup.map_eq_bot_iff_of_injective (H := pCore 2 ↥K)
      (f := Subgroup.inclusion hKH) (Subgroup.inclusion_injective hKH)).mp hmapbot)
  intro hbot
  have hmap := CFSG.ABGLocalTools.map_pCore_le_of_injective_of_normal (p := 2)
    (Subgroup.inclusion hHleS) (Subgroup.inclusion_injective hHleS) (by
      rw [Subgroup.inclusion_range]
      exact hHnorm)
  rw [hbot] at hmap
  have hmapbot : (pCore 2 ↥Hα).map (Subgroup.inclusion hHleS) = ⊥ := le_bot_iff.mp hmap
  exact hHcore ((Subgroup.map_eq_bot_iff_of_injective (H := pCore 2 ↥Hα)
    (f := Subgroup.inclusion hHleS) (Subgroup.inclusion_injective hHleS)).mp hmapbot)

private theorem le_socPre_of_odd_of_le_jHull {G : Type*} [Group G] [Finite G]
    {Ω : Type*} [MulAction G Ω] {D : HoltData G Ω} {B : Subgroup G}
    (hBH : B ≤ jHull G Ω) (hBodd : Odd (Nat.card B)) : B ≤ D.socPre := by
  classical
  let H : Subgroup G := jHull G Ω
  let R : Subgroup ↥H := D.socPre.subgroupOf H
  haveI : R.Normal := D.normal_socPre_subgroupOf
  let q : ↥H →* ↥H ⧸ R := QuotientGroup.mk' R
  let P : Subgroup ↥H := B.subgroupOf H
  have hPcard : Nat.card P = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv
  have hPodd : Odd (Nat.card P) := by rw [hPcard]; exact hBodd
  have hPbar_dvd_P : Nat.card (P.map q) ∣ Nat.card P := Subgroup.card_map_dvd (H := P) q
  have hPbar_dvd_index : Nat.card (P.map q) ∣ D.socPre.relIndex H := by
    have h := Subgroup.card_subgroup_dvd_card (P.map q)
    have hcard : Nat.card (↥H ⧸ R) = D.socPre.relIndex H := by
      rw [← Subgroup.index_eq_card]
      rfl
    simpa [hcard] using h
  have hPbar_dvd_two : Nat.card (P.map q) ∣ 2 :=
    hPbar_dvd_index.trans D.relIndex_socPre_jHull_dvd_two
  have hPbar_card : Nat.card (P.map q) = 1 :=
    Nat.eq_one_of_dvd_coprimes hPodd.coprime_two_right.symm hPbar_dvd_two hPbar_dvd_P
  have hPbar_bot : P.map q = ⊥ :=
    (Subgroup.eq_bot_iff_card (H := P.map q)).mpr hPbar_card
  have hPleker : P ≤ q.ker := (Subgroup.map_eq_bot_iff (H := P) (f := q)).mp hPbar_bot
  intro b hb
  have hbP : (⟨b, hBH hb⟩ : H) ∈ P := hb
  have hbker : (⟨b, hBH hb⟩ : H) ∈ q.ker := hPleker hbP
  rwa [QuotientGroup.ker_mk'] at hbker

private noncomputable def stabilizerPermEquiv {Δ : Type*} [Fintype Δ] [DecidableEq Δ]
    (M : Subgroup (Equiv.Perm Δ)) (b : Δ) :
    ↥(MulAction.stabilizer M b) ≃*
      ↥(M ⊓ MulAction.stabilizer (Equiv.Perm Δ) b) :=
  (Subgroup.equivMapOfInjective (MulAction.stabilizer M b) M.subtype
    M.subtype_injective).trans
    (MulEquiv.subgroupCongr (by
      rw [← MulAction.stabilizer_subgroupOf M b, Subgroup.subgroupOf_map_subtype, inf_comm]))

private theorem two_dvd_card_alternatingGroup_inf_stabilizer {Δ : Type*} [Fintype Δ]
    [DecidableEq Δ] (h7 : 7 ≤ Fintype.card Δ) (b : Δ) :
    2 ∣ Nat.card ↥(alternatingGroup Δ ⊓ MulAction.stabilizer (Equiv.Perm Δ) b) := by
  have h := two_mul_card_alternatingGroup_inf_stabilizer (by omega : 3 ≤ Fintype.card Δ) b
  have hdiv : 2 * 2 ∣ Nat.factorial (Fintype.card Δ - 1) :=
    Nat.dvd_factorial (by norm_num) (by omega)
  rw [← h] at hdiv
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) hdiv

private theorem eq_bot_of_odd_normal_of_alternating_stabilizer {Δ : Type*} [Fintype Δ]
    [DecidableEq Δ] (h7 : 7 ≤ Fintype.card Δ) (b : Δ)
    {N : Subgroup ↥(alternatingGroup Δ ⊓ MulAction.stabilizer (Equiv.Perm Δ) b)}
    (hNodd : Odd (Nat.card N)) (hNnorm : N.Normal) : N = ⊥ := by
  haveI : IsSimpleGroup ↥(alternatingGroup Δ ⊓ MulAction.stabilizer (Equiv.Perm Δ) b) :=
    isSimpleGroup_alternatingGroup_inf_stabilizer (by omega) b
  have heven : ¬ Odd (Nat.card ↥(alternatingGroup Δ ⊓
      MulAction.stabilizer (Equiv.Perm Δ) b)) := by
    have h := two_dvd_card_alternatingGroup_inf_stabilizer h7 b
    exact Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr h)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · rw [h, Subgroup.card_top] at hNodd
    exact absurd hNodd heven

private theorem eq_bot_of_odd_normal_stabilizer_alternating {Δ : Type*} [Fintype Δ]
    [DecidableEq Δ] (h7 : 7 ≤ Fintype.card Δ) (b : Δ)
    {N : Subgroup (alternatingGroup Δ)}
    (hNle : N ≤ MulAction.stabilizer (alternatingGroup Δ) b)
    (hNodd : Odd (Nat.card N))
    (hNnorm : (N.subgroupOf (MulAction.stabilizer (alternatingGroup Δ) b)).Normal) :
    N = ⊥ := by
  classical
  let T := MulAction.stabilizer (alternatingGroup Δ) b
  let e := stabilizerPermEquiv (alternatingGroup Δ) b
  let Nsub : Subgroup T := N.subgroupOf T
  have hNsubcard : Nat.card Nsub = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNle).toEquiv
  let Nimg : Subgroup ↥(alternatingGroup Δ ⊓
      MulAction.stabilizer (Equiv.Perm Δ) b) := Nsub.map e.toMonoidHom
  have hNimgodd : Odd (Nat.card Nimg) := by
    have hdvd : Nat.card Nimg ∣ Nat.card Nsub := Subgroup.card_map_dvd (H := Nsub) e.toMonoidHom
    exact Odd.of_dvd_nat (by rwa [hNsubcard]) hdvd
  have hNimgnorm : Nimg.Normal := hNnorm.map e.toMonoidHom e.surjective
  have hNimgbot : Nimg = ⊥ :=
    eq_bot_of_odd_normal_of_alternating_stabilizer h7 b hNimgodd hNimgnorm
  have hNsubbot : Nsub = ⊥ := by
    apply (Subgroup.map_eq_bot_iff_of_injective (H := Nsub) (f := e.toMonoidHom)
      e.injective).mp
    exact hNimgbot
  rw [eq_bot_iff]
  intro x hx
  have hxT : x ∈ T := hNle hx
  have hx' : (⟨x, hxT⟩ : T) ∈ Nsub := hx
  rw [hNsubbot] at hx'
  have hx1 : (⟨x, hxT⟩ : T) = 1 := Subgroup.mem_bot.mp hx'
  exact congrArg Subtype.val hx1

private theorem eq_bot_of_odd_normal_stabilizer_of_eq_alternating {Δ : Type*} [Fintype Δ]
    [DecidableEq Δ] {M : Subgroup (Equiv.Perm Δ)} (hM : M = alternatingGroup Δ)
    (h7 : 7 ≤ Fintype.card Δ) (b : Δ) {N : Subgroup M}
    (hNle : N ≤ MulAction.stabilizer M b)
    (hNodd : Odd (Nat.card N))
    (hNnorm : (N.subgroupOf (MulAction.stabilizer M b)).Normal) : N = ⊥ := by
  subst M
  exact eq_bot_of_odd_normal_stabilizer_alternating h7 b hNle hNodd hNnorm


private theorem coe_stabilizerEquiv {G : Type*} [Group G] [Finite G]
    {Ω : Type*} [MulAction G Ω] [Finite Ω] {D : HoltData G Ω}
    (hO : jOddCore G Ω = ⊥) (i : D.ι) (α : Ω)
    (k : ↥(D.L i ⊓ MulAction.stabilizer G α)) :
    ((stabilizerEquiv (D := D) hO i α k :
        ↥(MulAction.stabilizer (D.M i) (D.coord α i))) : D.M i) =
      D.lEquiv hO i ⟨k.1, k.2.1⟩ := rfl

private theorem exists_mem_L_apply_eq_of_mem_stabilizer {G : Type*} [Group G] [Finite G]
    {Ω : Type*} [MulAction G Ω] [Finite Ω] {D : HoltData G Ω}
    (hO : jOddCore G Ω = ⊥) (i : D.ι) (α : Ω) {m : D.M i}
    (hm : m ∈ MulAction.stabilizer (D.M i) (D.coord α i)) :
    ∃ l : D.L i, (l : G) • α = α ∧
      (D.lEquiv hO i l : Equiv.Perm (D.Ψc i)) = m := by
  obtain ⟨k, hk⟩ := (stabilizerEquiv (D := D) hO i α).surjective ⟨m, hm⟩
  refine ⟨⟨k.1, k.2.1⟩, k.2.2, ?_⟩
  have h1 : ((stabilizerEquiv (D := D) hO i α k :
      ↥(MulAction.stabilizer (D.M i) (D.coord α i))) : D.M i) = m :=
    congrArg Subtype.val hk
  have h2 : (((stabilizerEquiv (D := D) hO i α k :
      ↥(MulAction.stabilizer (D.M i) (D.coord α i))) : D.M i) : Equiv.Perm (D.Ψc i)) =
      (m : Equiv.Perm (D.Ψc i)) := congrArg (fun x : D.M i => (x : Equiv.Perm (D.Ψc i))) h1
  simpa [coe_stabilizerEquiv, D.coe_lEquiv_apply] using h2

private theorem smul_eq_self_of_mem_L_of_fixes_coord {G : Type*} [Group G] [Finite G]
    {Ω : Type*} [MulAction G Ω] [Finite Ω] {D : HoltData G Ω}
    (hO : jOddCore G Ω = ⊥) (i : D.ι) (l : D.L i) (ω : Ω)
    (h : ((D.lEquiv hO i l : D.M i) : Equiv.Perm (D.Ψc i)) (D.coord ω i) =
      D.coord ω i) : (l : G) • ω = ω := by
  apply D.coord_injective hO
  funext j
  by_cases hji : j = i
  · subst j
    have hc := D.coord_smul (⟨(l : G), D.L_le i l.2⟩ : jHull G Ω) ω i
    rw [← D.coe_lEquiv_apply (hO := hO) i l, h] at hc
    exact hc
  · have hc := D.coord_smul (⟨(l : G), D.L_le i l.2⟩ : jHull G Ω) ω j
    rw [D.rho_eq_one_of_mem_L (i := i) (j := j) (fun h => hji h.symm) l.2,
      Equiv.Perm.one_apply] at hc
    exact hc

private theorem coord_smul_eq_of_coord_eq {G : Type*} [Group G] [Finite G]
    {Ω : Type*} [MulAction G Ω] [Finite Ω] {D : HoltData G Ω}
    (hO : jOddCore G Ω = ⊥) (α : Ω)
    (hAlt : ∀ i, D.M i = alternatingGroup (D.Ψc i) ∧ 7 ≤ Fintype.card (D.Ψc i))
    {x : G}
    (hcomm : ∀ h ∈ jHull G Ω ⊓ MulAction.stabilizer G α, x * h = h * x)
    (ω : Ω) (i : D.ι) (haw : D.coord α i = D.coord ω i) :
    D.coord (x • ω) i = D.coord ω i := by
  classical
  set a : D.Ψc i := D.coord α i with ha
  set w : D.Ψc i := D.coord ω i with hw
  set g : D.Ψc i := D.coord (x • ω) i with hg
  have haw' : a = w := haw
  by_contra hne
  have hga : g ≠ a := fun h => hne (h.trans haw')
  have hcard : 5 ≤ Fintype.card (D.Ψc i) := (hAlt i).2.trans' (by omega)
  obtain ⟨δ, -, hδ⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a, g} : Finset (D.Ψc i))) (t := Finset.univ)
    (by rw [Finset.card_univ]; exact Finset.card_le_two.trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hδ
  obtain ⟨hδa, hδg⟩ := hδ
  obtain ⟨m, hmA, hma, hmg⟩ := exists_mem_alternatingGroup_fix_apply_eq
    (by omega : 4 ≤ Fintype.card (D.Ψc i)) hga hδa
  have hmg' : m g ≠ g := by rw [hmg]; exact hδg
  have hmM : m ∈ D.M i := by rw [(hAlt i).1]; exact hmA
  have hmstab : (⟨m, hmM⟩ : D.M i) ∈ MulAction.stabilizer (D.M i) a := by
    refine mem_stabilizer_iff.mpr ?_
    simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hma
  obtain ⟨l, hlα, hlm⟩ := exists_mem_L_apply_eq_of_mem_stabilizer hO i α hmstab
  have hlω : (l : G) • ω = ω := by
    apply smul_eq_self_of_mem_L_of_fixes_coord hO i l ω
    rw [hlm]
    change (m : Equiv.Perm (D.Ψc i)) (D.coord ω i) = D.coord ω i
    rw [← hw, ← haw']
    exact hma
  have hlH : (l : G) ∈ jHull G Ω := D.L_le i l.2
  have hlS : (l : G) ∈ MulAction.stabilizer G α := mem_stabilizer_iff.mpr hlα
  have hcomm_l := hcomm (l : G) ⟨hlH, hlS⟩
  have hlγ : (l : G) • (x • ω) = x • ω := by
    calc (l : G) • (x • ω) = ((l : G) * x) • ω := by rw [mul_smul]
      _ = (x * (l : G)) • ω := by rw [hcomm_l.symm]
      _ = x • ((l : G) • ω) := by rw [mul_smul]
      _ = x • ω := by rw [hlω]
  have hcoord := D.coord_smul (⟨(l : G), D.L_le i l.2⟩ : jHull G Ω) (x • ω) i
  rw [hlγ] at hcoord
  have hρl : D.ρ i ⟨(l : G), D.L_le i l.2⟩ = m := by
    rw [← D.coe_lEquiv_apply (hO := hO) i l, hlm]
  rw [hρl] at hcoord
  exact hmg' hcoord.symm

private theorem coord_smul_mem_pair_of_coord_ne {G : Type*} [Group G] [Finite G]
    {Ω : Type*} [MulAction G Ω] [Finite Ω] {D : HoltData G Ω}
    (hO : jOddCore G Ω = ⊥) (α : Ω)
    (hAlt : ∀ i, D.M i = alternatingGroup (D.Ψc i) ∧ 7 ≤ Fintype.card (D.Ψc i))
    {x : G}
    (hcomm : ∀ h ∈ jHull G Ω ⊓ MulAction.stabilizer G α, x * h = h * x)
    (ω : Ω) (i : D.ι) (hne : D.coord α i ≠ D.coord ω i) :
    D.coord (x • ω) i = D.coord α i ∨ D.coord (x • ω) i = D.coord ω i := by
  classical
  have h7i : 7 ≤ Fintype.card (D.Ψc i) := (hAlt i).2
  set a : D.Ψc i := D.coord α i with ha
  set w : D.Ψc i := D.coord ω i with hw
  set g : D.Ψc i := D.coord (x • ω) i with hg
  have hne' : a ≠ w := hne
  by_contra hnot
  push Not at hnot
  obtain ⟨hga, hgw⟩ := hnot
  obtain ⟨δ, -, hδ⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a, w, g} : Finset (D.Ψc i))) (t := Finset.univ)
    (by rw [Finset.card_univ]; exact Finset.card_le_three.trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hδ
  obtain ⟨hδa, hδw, hδg⟩ := hδ
  obtain ⟨m, hmA, hma, hmw, hmg⟩ := exists_mem_alternatingGroup_fix_two_apply_eq
    (by omega : 5 ≤ Fintype.card (D.Ψc i)) hga hgw hδa hδw
  have hmg' : m g ≠ g := by rw [hmg]; exact hδg
  have hmM : m ∈ D.M i := by rw [(hAlt i).1]; exact hmA
  have hmstab : (⟨m, hmM⟩ : D.M i) ∈ MulAction.stabilizer (D.M i) a := by
    refine mem_stabilizer_iff.mpr ?_
    simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hma
  obtain ⟨l, hlα, hlm⟩ := exists_mem_L_apply_eq_of_mem_stabilizer hO i α hmstab
  have hlω : (l : G) • ω = ω := by
    apply smul_eq_self_of_mem_L_of_fixes_coord hO i l ω
    rw [hlm]
    change (m : Equiv.Perm (D.Ψc i)) (D.coord ω i) = D.coord ω i
    rw [← hw, hmw]
  have hlH : (l : G) ∈ jHull G Ω := D.L_le i l.2
  have hlS : (l : G) ∈ MulAction.stabilizer G α := mem_stabilizer_iff.mpr hlα
  have hcomm_l := hcomm (l : G) ⟨hlH, hlS⟩
  have hlγ : (l : G) • (x • ω) = x • ω := by
    calc (l : G) • (x • ω) = ((l : G) * x) • ω := by rw [mul_smul]
      _ = (x * (l : G)) • ω := by rw [hcomm_l.symm]
      _ = x • ((l : G) • ω) := by rw [mul_smul]
      _ = x • ω := by rw [hlω]
  have hcoord := D.coord_smul (⟨(l : G), D.L_le i l.2⟩ : jHull G Ω) (x • ω) i
  rw [hlγ] at hcoord
  have hρl : D.ρ i ⟨(l : G), D.L_le i l.2⟩ = m := by
    rw [← D.coe_lEquiv_apply (hO := hO) i l, hlm]
  rw [hρl] at hcoord
  exact hmg' hcoord.symm

private theorem coord_smul_eq_of_coord_ne {G : Type*} [Group G] [Finite G]
    {Ω : Type*} [MulAction G Ω] [Finite Ω] {D : HoltData G Ω}
    (hO : jOddCore G Ω = ⊥) (α : Ω)
    (hAlt : ∀ i, D.M i = alternatingGroup (D.Ψc i) ∧ 7 ≤ Fintype.card (D.Ψc i))
    {x : G}
    (hcomm : ∀ h ∈ jHull G Ω ⊓ MulAction.stabilizer G α, x * h = h * x)
    (ω : Ω) (i : D.ι) (hne : D.coord α i ≠ D.coord ω i) :
    D.coord (x • ω) i = D.coord ω i := by
  classical
  have h7i : 7 ≤ Fintype.card (D.Ψc i) := (hAlt i).2
  have hp := coord_smul_mem_pair_of_coord_ne hO α hAlt hcomm ω i hne
  rcases hp with hga | hgw
  · exfalso
    set a : D.Ψc i := D.coord α i with ha
    set w : D.Ψc i := D.coord ω i with hw
    obtain ⟨δ, -, hδ⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({a, w} : Finset (D.Ψc i))) (t := Finset.univ)
      (by rw [Finset.card_univ]; exact Finset.card_le_two.trans_lt (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hδ
    obtain ⟨hδa, hδw⟩ := hδ
    obtain ⟨m, hmA, hma, hmw⟩ := exists_mem_alternatingGroup_fix_apply_eq
      (by omega : 4 ≤ Fintype.card (D.Ψc i)) hne.symm hδa
    have hmM : m ∈ D.M i := by rw [(hAlt i).1]; exact hmA
    have hmstab : (⟨m, hmM⟩ : D.M i) ∈ MulAction.stabilizer (D.M i) a := by
      refine mem_stabilizer_iff.mpr ?_
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hma
    obtain ⟨l, hlα, hlm⟩ := exists_mem_L_apply_eq_of_mem_stabilizer hO i α hmstab
    have hlγ : (l : G) • (x • ω) = x • ω := by
      apply smul_eq_self_of_mem_L_of_fixes_coord hO i l (x • ω)
      rw [hlm]
      change (m : Equiv.Perm (D.Ψc i)) (D.coord (x • ω) i) = D.coord (x • ω) i
      rw [hga]
      exact hma
    have hlH : (l : G) ∈ jHull G Ω := D.L_le i l.2
    have hlS : (l : G) ∈ MulAction.stabilizer G α := mem_stabilizer_iff.mpr hlα
    have hcomm_l := hcomm (l : G) ⟨hlH, hlS⟩
    have hxlω : x • ((l : G) • ω) = x • ω := by
      calc x • ((l : G) • ω) = (x * (l : G)) • ω := by rw [mul_smul]
        _ = ((l : G) * x) • ω := by rw [hcomm_l]
        _ = (l : G) • (x • ω) := by rw [mul_smul]
        _ = x • ω := hlγ
    have hlω : (l : G) • ω = ω := smul_left_cancel x hxlω
    have hcoordl : D.coord ((l : G) • ω) i = δ := by
      have hc := D.coord_smul (⟨(l : G), D.L_le i l.2⟩ : jHull G Ω) ω i
      rw [← D.coe_lEquiv_apply (hO := hO) i l, hlm] at hc
      rw [hc]
      change (m : Equiv.Perm (D.Ψc i)) w = δ
      rw [hmw]
    have hwδ : D.coord ω i = δ := by rw [← hcoordl, hlω]
    exact hδw (hw.trans hwδ).symm
  · exact hgw

private theorem eq_one_of_mem_primeCore_map_of_centralizes {G : Type*} [Group G] [Finite G]
    {Ω : Type*} [MulAction G Ω] [Finite Ω] [FaithfulSMul G Ω] {D : HoltData G Ω}
    (hO : jOddCore G Ω = ⊥) (α : Ω)
    (hAlt : ∀ i, D.M i = alternatingGroup (D.Ψc i) ∧ 7 ≤ Fintype.card (D.Ψc i))
    {x : G} (hx : x ∈ (pPrimeCore 2 ↥(MulAction.stabilizer G α)).map
      (MulAction.stabilizer G α).subtype)
    (hcomm : ∀ h ∈ jHull G Ω ⊓ MulAction.stabilizer G α, x * h = h * x) :
    x = 1 := by
  classical
  have hxS : x ∈ MulAction.stabilizer G α := by
    obtain ⟨b, -, rfl⟩ := hx
    exact b.2
  have hxα : x • α = α := mem_stabilizer_iff.mp hxS
  have hfix : ∀ ω : Ω, x • ω = ω := by
    intro ω
    have hcoord : D.coord (x • ω) = D.coord ω := by
      funext i
      by_cases h : D.coord α i = D.coord ω i
      · exact coord_smul_eq_of_coord_eq hO α hAlt hcomm ω i h
      · exact coord_smul_eq_of_coord_ne hO α hAlt hcomm ω i h
    have hmem : x • ω ∈ orbit (jOddCore G Ω) ω :=
      (D.coord_eq_iff ω (x • ω)).mp hcoord.symm
    rwa [orbit_jOddCore_eq_singleton hO, Set.mem_singleton_iff] at hmem
  exact eq_of_smul_eq_smul (α := Ω) fun ω => by rw [hfix ω, one_smul]

private noncomputable def rhoComponentHom {G : Type*} [Group G] [Finite G]
    {Ω : Type*} [MulAction G Ω] [Finite Ω] {D : HoltData G Ω} (α : Ω)
    {B0 : Subgroup ↥(MulAction.stabilizer G α)}
    (hH : ∀ b : B0, (b : G) ∈ jHull G Ω)
    (hsoc : ∀ b : B0, (b : G) ∈ D.socPre) (i : D.ι) : B0 →* D.M i :=
  { toFun := fun b => ⟨D.ρ i ⟨(b : G), hH b⟩,
      D.rho_mem_M_of_mem_socPre (h := ⟨(b : G), hH b⟩) (hsoc b) i⟩
    map_one' := Subtype.ext (map_one _)
    map_mul' := fun a b => Subtype.ext (by
      simpa using map_mul (D.ρ i) (⟨(a : G), hH a⟩ : jHull G Ω)
        (⟨(b : G), hH b⟩ : jHull G Ω)) }

private theorem range_rhoComponentHom_eq_bot_of_normal {G : Type*} [Group G] [Finite G]
    {Ω : Type*} [MulAction G Ω] [Finite Ω] {D : HoltData G Ω}
    (hO : jOddCore G Ω = ⊥) (α : Ω)
    (hAlt : ∀ i, D.M i = alternatingGroup (D.Ψc i) ∧ 7 ≤ Fintype.card (D.Ψc i))
    {B0 : Subgroup ↥(MulAction.stabilizer G α)}
    (hodd : Odd (Nat.card B0)) (hnorm : B0.Normal)
    (hH : ∀ b : B0, (b : G) ∈ jHull G Ω)
    (hsoc : ∀ b : B0, (b : G) ∈ D.socPre)
    (hfix : ∀ b : B0, (b : G) • α = α)
    (i : D.ι) : (rhoComponentHom α hH hsoc i).range = ⊥ := by
  classical
  let bi : D.Ψc i := D.coord α i
  let ψ : B0 →* D.M i := rhoComponentHom α hH hsoc i
  let Ni : Subgroup (D.M i) := ψ.range
  have hNiodd : Odd (Nat.card Ni) := by
    have hdvd : Nat.card Ni ∣ Nat.card B0 := Subgroup.card_range_dvd ψ
    exact Odd.of_dvd_nat hodd hdvd
  have hNile : Ni ≤ MulAction.stabilizer (D.M i) bi := by
    intro x hx
    obtain ⟨b0, rfl⟩ := hx
    refine mem_stabilizer_iff.mpr ?_
    have hc : D.ρ i ⟨(b0 : G), hH b0⟩ (D.coord α i) = D.coord α i := by
      have h := D.coord_smul (⟨(b0 : G), hH b0⟩ : jHull G Ω) α i
      rw [hfix b0] at h
      exact h.symm
    simpa [ψ, rhoComponentHom, Subgroup.smul_def, Equiv.Perm.smul_def] using hc
  have hNinorm : (Ni.subgroupOf (MulAction.stabilizer (D.M i) bi)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNile]
    intro t ht
    obtain ⟨k, hk⟩ := (stabilizerEquiv (D := D) hO i α).surjective ⟨t, ht⟩
    let kL : D.L i := ⟨k.1, k.2.1⟩
    have hlt : D.lEquiv hO i kL = t := by
      exact congrArg Subtype.val hk
    have hρk : D.ρ i ⟨(k.1 : G), D.L_le i k.2.1⟩ =
        (t : Equiv.Perm (D.Ψc i)) := by
      rw [← D.coe_lEquiv_apply (hO := hO) i kL, hlt]
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro y ⟨x, hx, rfl⟩
      obtain ⟨b0, rfl⟩ := hx
      let s : ↥(MulAction.stabilizer G α) := ⟨(k.1 : G), k.2.2⟩
      let b' : B0 := ⟨s * (b0 : ↥(MulAction.stabilizer G α)) * s⁻¹,
        hnorm.conj_mem (b0 : ↥(MulAction.stabilizer G α)) b0.2 s⟩
      refine ⟨b', ?_⟩
      have hb'coe : ((b' : ↥(MulAction.stabilizer G α)) : G) =
          (k.1 : G) * ((b0 : ↥(MulAction.stabilizer G α)) : G) * (k.1 : G)⁻¹ := rfl
      have hj : (⟨((b' : ↥(MulAction.stabilizer G α)) : G), hH b'⟩ : jHull G Ω) =
          ⟨(k.1 : G), D.L_le i k.2.1⟩ * ⟨((b0 : ↥(MulAction.stabilizer G α)) : G), hH b0⟩ *
            (⟨(k.1 : G), D.L_le i k.2.1⟩ : jHull G Ω)⁻¹ := by
        apply Subtype.ext
        exact hb'coe
      have hψ : (ψ b' : D.M i) = t * ψ b0 * t⁻¹ := by
        apply Subtype.ext
        change D.ρ i ⟨((b' : ↥(MulAction.stabilizer G α)) : G), hH b'⟩ =
          (t : Equiv.Perm (D.Ψc i)) * D.ρ i
            ⟨((b0 : ↥(MulAction.stabilizer G α)) : G), hH b0⟩ *
            (t : Equiv.Perm (D.Ψc i))⁻¹
        rw [hj, map_mul, map_mul, map_inv, hρk]
      rw [hψ]
      rfl
    · rw [Subgroup.card_map_of_injective (MulAut.conj t).injective]
  exact eq_bot_of_odd_normal_stabilizer_of_eq_alternating (hAlt i).1 (hAlt i).2 bi
    hNile hNiodd hNinorm

private theorem rho_eq_one_of_odd_normal_stabilizer {G : Type*} [Group G] [Finite G]
    {Ω : Type*} [MulAction G Ω] [Finite Ω] {D : HoltData G Ω}
    (hO : jOddCore G Ω = ⊥) (α : Ω)
    (hAlt : ∀ i, D.M i = alternatingGroup (D.Ψc i) ∧ 7 ≤ Fintype.card (D.Ψc i))
    {B0 : Subgroup ↥(MulAction.stabilizer G α)}
    (hodd : Odd (Nat.card B0)) (hnorm : B0.Normal)
    (hH : ∀ b : B0, (b : G) ∈ jHull G Ω)
    (hsoc : ∀ b : B0, (b : G) ∈ D.socPre)
    (hfix : ∀ b : B0, (b : G) • α = α)
    (i : D.ι) (b : B0) : D.ρ i ⟨(b : G), hH b⟩ = 1 := by
  have hbot := range_rhoComponentHom_eq_bot_of_normal hO α hAlt hodd hnorm hH hsoc hfix i
  have h1 : rhoComponentHom α hH hsoc i b = 1 := by
    rw [MonoidHom.range_eq_bot_iff.mp hbot]
    rfl
  have hval : (rhoComponentHom α hH hsoc i b : Equiv.Perm (D.Ψc i)) = 1 :=
    congrArg Subtype.val h1
  simpa [rhoComponentHom] using hval

private theorem pPrimeCore_stabilizer_eq_bot_of_all_alternating {G : Type*} [Group G] [Finite G]
    {Ω : Type*} [MulAction G Ω] [Finite Ω] [FaithfulSMul G Ω] {D : HoltData G Ω}
    (hO : jOddCore G Ω = ⊥) (α : Ω)
    (hAlt : ∀ i, D.M i = alternatingGroup (D.Ψc i) ∧ 7 ≤ Fintype.card (D.Ψc i)) :
    pPrimeCore 2 ↥(MulAction.stabilizer G α) = ⊥ := by
  classical
  let S : Subgroup G := MulAction.stabilizer G α
  let B : Subgroup ↥S := pPrimeCore 2 ↥S
  let Hα : Subgroup ↥S := (jHull G Ω).subgroupOf S
  let B0 : Subgroup ↥S := B ⊓ Hα
  have hBodd : Odd (Nat.card B) :=
    Nat.Coprime.odd_of_left (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥S))
  have hB0odd : Odd (Nat.card B0) :=
    Odd.of_dvd_nat hBodd (Subgroup.card_dvd_of_le inf_le_left)
  have hB0norm : B0.Normal := Subgroup.normal_inf_normal B Hα
  have hB0H : ∀ b : B0, ((b : ↥S) : G) ∈ jHull G Ω := fun b => b.2.2
  have hB0fix : ∀ b : B0, ((b : ↥S) : G) • α = α := fun b => b.1.2
  have hB0soc : ∀ b : B0, ((b : ↥S) : G) ∈ D.socPre := by
    have hB0Godd : Odd (Nat.card (B0.map S.subtype)) := by
      rw [Subgroup.card_map_of_injective S.subtype_injective]
      exact hB0odd
    have hB0GH : B0.map S.subtype ≤ jHull G Ω := by
      rintro x ⟨b, hb, rfl⟩
      exact hB0H ⟨b, hb⟩
    have hle := le_socPre_of_odd_of_le_jHull (D := D) hB0GH hB0Godd
    intro b
    exact hle (Subgroup.mem_map_of_mem S.subtype b.2)
  have hB0triv : B0 = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    have hρ : ∀ i, D.ρ i ⟨((b : ↥S) : G), hB0H ⟨b, hb⟩⟩ = 1 := fun i =>
      rho_eq_one_of_odd_normal_stabilizer hO α hAlt hB0odd hB0norm hB0H hB0soc hB0fix i
        ⟨b, hb⟩
    have hker : ((⟨((b : ↥S) : G), hB0H ⟨b, hb⟩⟩ : jHull G Ω) : G) ∈ jOrbitKernel G Ω :=
      (D.mem_jOrbitKernel_iff_rho (h := ⟨((b : ↥S) : G), hB0H ⟨b, hb⟩⟩)).mpr hρ
    rw [jOrbitKernel_eq_bot hO, Subgroup.mem_bot] at hker
    exact Subtype.ext (by simpa using hker)
  have hB0Gbot : B0.map S.subtype = ⊥ := by rw [hB0triv, Subgroup.map_bot]
  have hcomm : ∀ x ∈ B.map S.subtype, ∀ h ∈ jHull G Ω ⊓ S, x * h = h * x := by
    intro x hx h hh
    obtain ⟨b, hb, rfl⟩ := hx
    let hS : ↥S := ⟨h, hh.2⟩
    have hbconj : hS * b⁻¹ * hS⁻¹ ∈ B :=
      (CFSG.pPrimeCore_normal (G := ↥S)).conj_mem (b⁻¹) (B.inv_mem hb) hS
    have hcS : b * hS * b⁻¹ * hS⁻¹ ∈ B := by
      rw [show b * hS * b⁻¹ * hS⁻¹ = b * (hS * b⁻¹ * hS⁻¹) by group]
      exact B.mul_mem hb hbconj
    have hcH : ⁅(b : G), h⁆ ∈ jHull G Ω := by
      have h1 : (b : G) * h * (b : G)⁻¹ ∈ jHull G Ω :=
        jHull_normal.conj_mem h hh.1 (b : G)
      rw [show ⁅(b : G), h⁆ = ((b : G) * h * (b : G)⁻¹) * h⁻¹ by group]
      exact (jHull G Ω).mul_mem h1 ((jHull G Ω).inv_mem hh.1)
    have hcS_H : b * hS * b⁻¹ * hS⁻¹ ∈ Hα := by
      change (((b * hS * b⁻¹ * hS⁻¹ : ↥S) : G)) ∈ jHull G Ω
      simpa [commutatorElement_def, mul_assoc] using hcH
    have hcB0 : ⁅(b : G), h⁆ ∈ B0.map S.subtype := by
      have hc0 : b * hS * b⁻¹ * hS⁻¹ ∈ B0 := Subgroup.mem_inf.mpr ⟨hcS, hcS_H⟩
      have hmap := Subgroup.mem_map_of_mem S.subtype hc0
      simpa [commutatorElement_def, mul_assoc] using hmap
    have hc1 : ⁅(b : G), h⁆ = 1 := by
      rw [hB0Gbot, Subgroup.mem_bot] at hcB0
      exact hcB0
    exact commutatorElement_eq_one_iff_mul_comm.mp hc1
  have hBbot : B.map S.subtype = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact (eq_one_of_mem_primeCore_map_of_centralizes hO α hAlt hx
      (hcomm x hx)).symm ▸ Subgroup.one_mem _
  exact (Subgroup.map_eq_bot_iff_of_injective (H := B) (f := S.subtype)
    S.subtype_injective).mp hBbot

namespace HoltData

theorem pPrimeCore_stabilizer_eq_bot_or_pCore_ne_bot
    {G : Type*} [Group G] [Finite G] {Ω : Type*} [MulAction G Ω] [Finite Ω] [FaithfulSMul G Ω]
    (D : HoltData G Ω) (hO : jOddCore G Ω = ⊥) (α : Ω) :
    pPrimeCore 2 ↥(MulAction.stabilizer G α) = ⊥ ∨
      pCore 2 ↥(MulAction.stabilizer G α) ≠ ⊥ := by
  classical
  by_cases hSE : ∃ i, IsNaturalSE (D.M i)
  · right
    obtain ⟨i, hi⟩ := hSE
    exact pCore_stabilizer_ne_bot_of_isNaturalSE (D := D) hO α hi
  · left
    push Not at hSE
    refine pPrimeCore_stabilizer_eq_bot_of_all_alternating (D := D) hO α fun i => ?_
    rcases D.factor i with hAlt | hSEi
    · exact hAlt
    · exact absurd hSEi (hSE i)

end HoltData

end CFSG.Holt.H78

end
