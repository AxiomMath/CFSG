module

public import CFSG.Certificates.Kernel.FiveStdKOrbSound
public import CFSG.GH74.GLS.LU.Local.FiveStdDiag

public section

namespace CFSG.KC.FiveStdK

open CFSG.GH74.GLS.LU.Local.FiveStd CFSG.GH74.GLS.LU.Local.Five CFSG.GH74.GLS.LU.Local.Five.FiveStdBase

open scoped Pointwise

variable {Gp : Type} [Group Gp]

theorem length_ppE_sq (x y : E) (p : Nat) : (ppE x y p p).length = p * p := by
  simp [ppE, mulLL, powers, Function.comp_def]

theorem conj_into_pp {ι : E → Gp} (hM : Model ι) (hK : Nat.card (vSub hM) = 28800) {p : Nat}
    [hp : Fact p.Prime] (hidx : ¬ p ∣ 28800 / (p * p)) (hpp : p * p ∣ 28800)
    {x y : E} (hx : validE x = true) (hy : validE y = true) (hxy : mulE x y = mulE y x)
    (hxp : powE x p = oneE) (hyp : powE y p = oneE) (hnd : (ppE x y p p).Nodup)
    {g : E} (hg : validE g = true) (hgp : powE g p = oneE) :
    ∃ c, validE c = true ∧ ∃ i < p, ∃ j < p, g = conjE c (mulE (powE x i) (powE y j)) := by
  have hp0 : 0 < p := hp.out.pos
  set K := vSub hM with hKd
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have hxy' : ι x * ι y = ι y * ι x := by
    rw [← hM.map_mul _ _ hx hy, ← hM.map_mul _ _ hy hx, hxy]
  have hxp' : ι x ^ p = 1 := by rw [← hM.map_powE hx, hxp, hM.map_one]
  have hyp' : ι y ^ p = 1 := by rw [← hM.map_powE hy, hyp, hM.map_one]
  obtain ⟨P, hP⟩ := FiveStdDiag.exists_pp_sub_gen hp0 hxy' hxp' hyp'
  have hPS : (P : Set Gp) = S ι (ppE x y p p) := by
    ext h
    rw [SetLike.mem_coe, hP, hM.S_ppE hx hy, Set.mem_setOf_eq]
    constructor
    · rintro ⟨i, j, rfl⟩
      refine ⟨i % p, Nat.mod_lt _ hp0, j % p, Nat.mod_lt _ hp0, ?_⟩
      rw [← pow_eq_pow_mod i hxp', ← pow_eq_pow_mod j hyp']
    · rintro ⟨i, -, j, -, rfl⟩
      exact ⟨i, j, rfl⟩
  have hPK : P ≤ K := by
    intro h hh
    obtain ⟨i, j, rfl⟩ := (hP h).1 hh
    refine ⟨mulE (powE x i) (powE y j), hM.valid_mul _ _ (hM.valid_powE hx i) (hM.valid_powE hy j), ?_⟩
    rw [hM.map_mul _ _ (hM.valid_powE hx i) (hM.valid_powE hy j), hM.map_powE hx, hM.map_powE hy]
  have hPc : Nat.card P = p * p := by
    rw [natCard_eq_of_coe P hPS, natCard_S hM (hM.V_ppE hx hy p p) hnd, length_ppE_sq]
  have hcardP1 : Nat.card ↥(P.subgroupOf K) = p * p := by
    rw [Nat.card_congr (P.subgroupOfEquivOfLe hPK).toEquiv, hPc]
  have hP1p : IsPGroup p ↥(P.subgroupOf K) := IsPGroup.of_card (n := 2) (by rw [hcardP1]; ring)
  have hP1idx : ¬ p ∣ (P.subgroupOf K).index := by
    have hci := Subgroup.card_mul_index (P.subgroupOf K)
    rw [hcardP1, hK] at hci
    have hidx' : (P.subgroupOf K).index = 28800 / (p * p) := by
      rw [← hci, Nat.mul_div_cancel_left _ (Nat.mul_pos hp0 hp0)]
    rw [hidx']
    exact hidx
  let PA : Sylow p K := hP1p.toSylow hP1idx
  let g' : K := ⟨ι g, g, hg, rfl⟩
  have hgo : orderOf g' ∣ p := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    change ι g ^ p = 1
    rw [← hM.map_powE hg, hgp, hM.map_one]
  have hQ : IsPGroup p (Subgroup.zpowers g') := by
    rcases (Nat.dvd_prime hp.out).1 hgo with h1 | h1
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h1, pow_one])
  obtain ⟨PQ, hQle⟩ := hQ.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq K PA PQ
  have hc' : (MulAut.conj c • (P.subgroupOf K) : Subgroup K) = (PQ : Subgroup K) := by
    have := congrArg (fun Q : Sylow p K => (Q : Subgroup K)) hc
    simpa [PA, Sylow.coe_subgroup_smul] using this
  have hmem : g' ∈ MulAut.conj c • (P.subgroupOf K) := by
    rw [hc']
    exact hQle (Subgroup.mem_zpowers g')
  obtain ⟨s, hs, hsr⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hmem
  have hsP : (s : Gp) ∈ P := Subgroup.mem_subgroupOf.1 hs
  obtain ⟨i, j, hij⟩ := (hP _).1 hsP
  obtain ⟨cE, hcE, hcEe⟩ := (mem_vSub hM).1 c.2
  have hvi := hM.valid_powE hx (i % p)
  have hvj := hM.valid_powE hy (j % p)
  have hhv := hM.valid_mul _ _ hvi hvj
  refine ⟨cE, hcE, i % p, Nat.mod_lt _ hp0, j % p, Nat.mod_lt _ hp0, ?_⟩
  apply hM.inj _ _ hg (hM.valid_conjE hcE hhv)
  rw [hM.map_conjE hcE hhv, hM.map_mul _ _ hvi hvj, hM.map_powE hx, hM.map_powE hy,
    ← pow_eq_pow_mod i hxp', ← pow_eq_pow_mod j hyp', ← hij, hcEe]
  have := congrArg Subtype.val hsr
  simpa using this.symm

end CFSG.KC.FiveStdK

end
