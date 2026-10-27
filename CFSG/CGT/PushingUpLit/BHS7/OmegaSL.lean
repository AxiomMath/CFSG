module

public import CFSG.CGT.PushingUpLit.BHS7.OmegaCentral
public import CFSG.CGT.PushingUpLit.BHS7.BaumSylow
public import CFSG.CGT.PushingUpLit.BHS7.BorelMax

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T E : Subgroup Γ}

theorem isSylowTwoOf_inf_of_isSubnormal {T H L : Subgroup Γ}
    (h : CFSG.Open.IsSubnormal L H) : IsSylowTwoOf T H → IsSylowTwoOf (T ⊓ L) L := by
  induction h with
  | refl K =>
    intro hT
    rwa [inf_eq_left.mpr hT.1]
  | @step L M K hLM hN _ ih =>
    intro hT
    have h1 := ih hT
    have hnorm : M ≤ Subgroup.normalizer (L : Set Γ) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hN
    have h2 := B6.isSylowTwoOf_inf_normal h1 hLM hnorm
    rwa [inf_assoc, inf_eq_right.mpr hLM] at h2

theorem baum_le_autPre_sylow (hG : CharTwo G) (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E)
    {n : ℕ} (hn2 : 2 ≤ n) (hn : IsNaturalSLTwoModule ↥E n) (hS : IsSylowTwoOf (T ⊓ E) E) :
    baum T ≤ autPre (pCoreOf 2 E) (autOn (T ⊓ E) (pCoreOf 2 E)) := by
  classical
  set W : Subgroup Γ := pCoreOf 2 E with hWdef
  set S : Subgroup Γ := T ⊓ E with hSdef
  have hT2 : IsSylowTwoOf T G := isSylowTwoOf_of_isSylowOf hT
  have hEW : E ≤ Subgroup.normalizer (W : Set Γ) := le_normalizer_pCoreOf_self E
  have hBE : baum T ≤ Subgroup.normalizer (E : Set Γ) := baum_le_normalizer_of_isBTBlock hE
  have hBW : baum T ≤ Subgroup.normalizer (W : Set Γ) :=
    hBE.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 E)
  have hbs := (block_structure_sl hG hT hE hn2 hn).1
  rw [blockW_eq_pCoreOf hE] at hbs
  have hSE : S ≤ E := inf_le_right
  have hBT : baum T ≤ T := inf_le_left
  have hSW : S ≤ Subgroup.normalizer (W : Set Γ) := hSE.trans hEW
  set J : Subgroup Γ := baum T ⊔ S with hJdef
  have hJT : J ≤ T := sup_le hBT inf_le_left
  have hJW : J ≤ Subgroup.normalizer (W : Set Γ) := sup_le hBW hSW
  have hSA : autOn S W ≤ autOn E W := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_autOn_iff.mp hx
    exact mem_autOn_iff.mpr ⟨a, hSE ha, rfl⟩
  have hJA : autOn J W ≤ autOn E W := by
    rw [← le_autPre_iff hJW]
    exact sup_le ((le_autPre_iff hBW).mpr hbs) ((le_autPre_iff hSW).mpr hSA)
  have hρ := actOnRange_surjective W E hEW
  have hS0 : IsPGroup 2 (S.subgroupOf E) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P0 : Sylow 2 ↥E := hS0.toSylow hS.2.2
  let Q : Sylow 2 ↥(autOn E W) := P0.mapSurjective hρ
  have hQ : (Q : Subgroup ↥(autOn E W)) = (S.subgroupOf E).map (actOnRange W E hEW) := by
    simp [Q, P0]
  let U : Subgroup ↥(autOn E W) := (autOn J W).subgroupOf (autOn E W)
  have hU2 : IsPGroup 2 U := by
    intro u
    have hu : (u.1 : MulAut ↥W) ∈ autOn J W := Subgroup.mem_subgroupOf.mp u.2
    obtain ⟨a, ha, hau⟩ := mem_autOn_iff.mp hu
    obtain ⟨k, hk⟩ := hT2.2.1 ⟨(a : Γ), hJT ha⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have h1 : a ^ (2 ^ k) = 1 := Subtype.ext (by
      have := congrArg (fun z : ↥T => (z : Γ)) hk
      simpa using this)
    show (u.1 : MulAut ↥W) ^ (2 ^ k) = 1
    rw [← hau, ← map_pow, h1, map_one]
  have hQU : (Q : Subgroup ↥(autOn E W)) ≤ U := by
    intro q hq
    rw [hQ] at hq
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hq
    refine Subgroup.mem_subgroupOf.mpr (mem_autOn_iff.mpr ⟨Subgroup.inclusion hEW s, ?_, rfl⟩)
    exact (le_sup_right : S ≤ J) (Subgroup.mem_subgroupOf.mp hs)
  have hUQ : U = (Q : Subgroup ↥(autOn E W)) := Q.is_maximal' hU2 hQU
  intro b hb
  refine mem_autPre.mpr ⟨hBW hb, ?_⟩
  have hbA : conjAct W ⟨b, hBW hb⟩ ∈ autOn E W :=
    hbs (mem_autOn_iff.mpr ⟨⟨b, hBW hb⟩, hb, rfl⟩)
  have hbJ : conjAct W ⟨b, hBW hb⟩ ∈ autOn J W :=
    mem_autOn_iff.mpr ⟨⟨b, hBW hb⟩, (le_sup_left : baum T ≤ J) hb, rfl⟩
  have hbU : (⟨conjAct W ⟨b, hBW hb⟩, hbA⟩ : ↥(autOn E W)) ∈ U := Subgroup.mem_subgroupOf.mpr hbJ
  rw [hUQ, hQ] at hbU
  obtain ⟨s, hs, hsb⟩ := Subgroup.mem_map.mp hbU
  have hact : conjAct W (Subgroup.inclusion hEW s) = conjAct W ⟨b, hBW hb⟩ :=
    congrArg Subtype.val hsb
  rw [← hact]
  exact mem_autOn_iff.mpr ⟨Subgroup.inclusion hEW s, Subgroup.mem_subgroupOf.mp hs, rfl⟩

omit [Finite Γ] in
theorem exists_pow_two_eq_one_of_centralizes {E B : Subgroup Γ} [Finite Γ] (hchar : CharTwo E)
    (hW : ∀ x ∈ pCoreOf 2 E, ∀ y ∈ pCoreOf 2 E, x * y = y * x) (hB : IsPGroup 2 ↥B)
    (hBE : B ≤ Subgroup.normalizer (E : Set Γ)) {c : Γ} (hc : c ∈ E ⊔ B)
    (hcW : c ∈ Subgroup.centralizer (pCoreOf 2 E : Set Γ)) : ∃ k : ℕ, c ^ (2 ^ k) = 1 := by
  obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
  refine ⟨a, ?_⟩
  set y : Γ := c ^ (2 ^ a) with hy
  have hyord : orderOf y = m := by
    rw [hy, orderOf_pow_of_dvd (pow_ne_zero a two_ne_zero) ⟨m, hord⟩, hord]
    simp [Nat.mul_div_cancel_left _ (pow_pos two_pos a)]
  have hyH : y ∈ E ⊔ B := pow_mem hc _
  have hyE : y ∈ E := mem_of_odd_orderOf_sup hB hBE hyH (hyord ▸ hm)
  have hyW : y ∈ E ⊓ Subgroup.centralizer (pCoreOf 2 E : Set Γ) :=
    ⟨hyE, Subgroup.pow_mem _ hcW _⟩
  rw [inf_centralizer_pCoreOf_eq hchar hW] at hyW
  obtain ⟨k, hk⟩ := (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 E) ⟨y, hyW⟩
  have hyk : y ^ (2 ^ k) = 1 := by
    have := congrArg (fun z : ↥(pCoreOf 2 E) => (z : Γ)) hk
    simpa using this
  have hdvd : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hyk
  have hone : orderOf y = 1 := by
    have hodd : Odd (orderOf y) := hyord ▸ hm
    exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd))
      hdvd
  exact orderOf_eq_one_iff.mp hone

theorem isPGroup_inf_autPre (hG : CharTwo G) (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E) :
    IsPGroup 2 ↥((E ⊔ baum T) ⊓
      autPre (pCoreOf 2 E) (autOn (T ⊓ E) (pCoreOf 2 E))) := by
  classical
  set W : Subgroup Γ := pCoreOf 2 E with hWdef
  have hT2 : IsSylowTwoOf T G := isSylowTwoOf_of_isSylowOf hT
  have hchar : CharTwo E := charTwo_of_isBTBlock hG hT hE
  have hBE : baum T ≤ Subgroup.normalizer (E : Set Γ) := baum_le_normalizer_of_isBTBlock hE
  have hB2 : IsPGroup 2 ↥(baum T) :=
    hT2.2.1.of_injective _ (Subgroup.inclusion_injective inf_le_left)
  intro x
  have hxH : (x : Γ) ∈ E ⊔ baum T := x.2.1
  obtain ⟨hxN, hxS⟩ := mem_autPre.mp x.2.2
  obtain ⟨a, ha, hax⟩ := mem_autOn_iff.mp hxS
  obtain ⟨k, hk⟩ := hT2.2.1 ⟨(a : Γ), ha.1⟩
  have h1 : conjAct W ((⟨(x : Γ), hxN⟩ : ↥(Subgroup.normalizer (W : Set Γ))) ^ (2 ^ k)) = 1 := by
    rw [map_pow, ← hax, ← map_pow]
    have : a ^ (2 ^ k) = 1 := Subtype.ext (by
      have := congrArg (fun z : ↥T => (z : Γ)) hk
      simpa using this)
    rw [this, map_one]
  have hc : (x : Γ) ^ (2 ^ k) ∈ Subgroup.centralizer (W : Set Γ) :=
    (conjAct_eq_one_iff W _).mp h1
  obtain ⟨j, hj⟩ := exists_pow_two_eq_one_of_centralizes hchar hE.elemAbelian.1 hB2 hBE
    (pow_mem hxH _) hc
  refine ⟨k + j, Subtype.ext ?_⟩
  show (x : Γ) ^ (2 ^ (k + j)) = 1
  rw [pow_add, pow_mul]
  exact hj

theorem omega_cstar_sl (h : MinCex G T) {E : Subgroup Γ} (hE : E ∈ omegaSet G T) {n : ℕ}
    (hn2 : 2 ≤ n) (hn : IsNaturalSLTwoModule ↥E n) :
    cStarIn G T ⊓ E = Subgroup.normalizer ((T ⊓ E : Subgroup Γ) : Set Γ) ⊓ E := by
  classical
  have hG := h.charTwo
  have hT : IsSylowOf 2 T G := h.sylow
  have hT2 : IsSylowTwoOf T G := isSylowTwoOf_of_isSylowOf hT
  have hEb : IsBTBlock G T E := omega_isBTBlock h hE
  have hEG : E ≤ G := hEb.le
  set W : Subgroup Γ := pCoreOf 2 E with hWdef
  set S : Subgroup Γ := T ⊓ E with hSdef
  have hEW : E ≤ Subgroup.normalizer (W : Set Γ) := le_normalizer_pCoreOf_self E
  have hchar : CharTwo E := charTwo_of_isBTBlock hG hT hEb
  have hb0 : baum T ≠ ⊥ := fun h0 => h.ne (cStarIn_eq_of_baum_eq_bot h0)
  have hS : IsSylowTwoOf S E := isSylowTwoOf_inf_of_isSubnormal hE.2 hT2
  have hWS : W ≤ S :=
    le_inf (pCoreOf_le_sylow hG hT hEb hT) (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 E)
  have hnat := isNatSL_of_isBTBlock hG hT hEb hn
  rw [blockW_eq_pCoreOf hEb] at hnat
  obtain ⟨φ, ψ, hφs, hφk, -, -, -⟩ := hnat
  have hker : φ.ker ≤ S.subgroupOf E := by
    rw [hφk, inf_centralizer_pCoreOf_eq hchar hEb.elemAbelian.1]
    exact fun x hx => Subgroup.mem_subgroupOf.mpr (hWS (Subgroup.mem_subgroupOf.mp hx))
  set H : Subgroup Γ := E ⊔ baum T with hHdef
  set P : Subgroup Γ := H ⊓ autPre W (autOn S W) with hPdef
  have hP2 : IsPGroup 2 ↥P := isPGroup_inf_autPre hG hT hEb
  have hHG : H ≤ G := sup_le hEG ((inf_le_left : baum T ≤ T).trans hT2.1)
  have hPG : P ≤ G := inf_le_left.trans hHG
  have hBP : baum T ≤ P :=
    le_inf le_sup_right (baum_le_autPre_sylow hG hT hEb hn2 hn hS)
  have hconj : ∀ g ∈ Subgroup.normalizer (S : Set Γ) ⊓ E, ∀ x ∈ P, g * x * g⁻¹ ∈ P := by
    intro g hg x hx
    have hgH : g ∈ H := (le_sup_left : E ≤ H) hg.2
    exact ⟨H.mul_mem (H.mul_mem hgH hx.1) (H.inv_mem hgH),
      conj_mem_autPre (hEW hg.2) hg.1 hx.2⟩
  have hN : Subgroup.normalizer (S : Set Γ) ⊓ E ≤ cStarIn G T := by
    intro g hg
    have hgP : g ∈ Subgroup.normalizer (P : Set Γ) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨fun hx => hconj g hg x hx, fun hx => ?_⟩
      have := hconj g⁻¹ ((Subgroup.normalizer (S : Set Γ) ⊓ E).inv_mem hg) _ hx
      have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
      rwa [e] at this
    exact inf_normalizer_baum_le_cStarIn hb0
      ⟨hEG hg.2, mem_normalizer_baum_of_pGroup hT2 hP2 hPG hBP (hEG hg.2) hgP⟩
  rcases normalizer_inf_maximal_of_sl2 hS φ hφs hker (K := cStarIn G T ⊓ E) inf_le_right
    (le_inf hN inf_le_right) with h1 | h1
  · exact h1
  · exact absurd (inf_eq_right.mp h1) (omega_not_le_cStarIn h hE)

end CFSG.CGT.PushingUpLit.BHS7
