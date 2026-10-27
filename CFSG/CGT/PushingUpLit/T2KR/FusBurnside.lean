module

public import CFSG.CGT.PushingUpLit.T2K.SixA
public import CFSG.CGT.Timmesfeld75.WeaklyClosed

public section

namespace CFSG.CGT.PushingUpLit.T2KR

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.T2K CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_isSylowOf_ge_of_isPGroup {H P : Subgroup G} (hP : IsPGroup 2 P) (hPH : P ≤ H) :
    ∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 S H ∧ P ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := (hP.comap_subtype (K := H)).exists_le_sylow
  refine ⟨(S : Subgroup H).map H.subtype, ⟨S, rfl⟩, fun p hp => ?_⟩
  exact ⟨⟨p, hPH hp⟩, hS (show (⟨p, hPH hp⟩ : ↥H) ∈ P.subgroupOf H from hp), rfl⟩

theorem exists_conj_of_conj_mem_Q {L M T : Subgroup G} {n : ℕ} (hs : Sec6 G L M T n) {x h : G}
    (hx : x ∈ QOf L M) (hy : h * x * h⁻¹ ∈ QOf L M) :
    ∃ m ∈ M, h * x * h⁻¹ = m * x * m⁻¹ := by
  classical
  set Q := QOf L M with hQ
  have hQ2 : IsPGroup 2 Q := isPGroup_two_of_isElemAbelian hs.Q_abelian
  have hcomm : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := fun a ha b hb =>
    elemAbelian_mul_comm hs.Q_abelian ha hb
  set C : Subgroup G := Subgroup.centralizer ({x} : Set G) with hC
  have hQC : Q ≤ C := fun q hq =>
    Subgroup.mem_centralizer_singleton_iff.2 (hcomm x hx q hq).symm
  set Q' : Subgroup G := Q.map (MulAut.conj h⁻¹).toMonoidHom with hQ'
  have hQ'2 : IsPGroup 2 Q' := hQ2.map _
  have hQ'C : Q' ≤ C := by
    rintro _ ⟨q, hq, rfl⟩
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    have h2 := hcomm q hq _ hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc (h⁻¹ * q * h) * x = h⁻¹ * (q * (h * x * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * x * h⁻¹) * q) * h := by rw [h2]
      _ = x * (h⁻¹ * q * h) := by group
  obtain ⟨P, hPsyl, hQP⟩ := exists_isSylowOf_ge_of_isPGroup hQ2 hQC
  obtain ⟨c, hcC, hc⟩ := exists_conj_le_of_isPGroup hPsyl hQ'2 hQ'C
  obtain ⟨T₂, hT₂, hPT₂⟩ := exists_isSylowOf_ge_of_isPGroup hPsyl.isPGroup (le_top : P ≤ ⊤)
  obtain ⟨k, -, hk⟩ := exists_conj_le_of_isPGroup hs.sec4.sylowG hT₂.isPGroup (le_top : T₂ ≤ ⊤)
  have hQk : Q.map (MulAut.conj k).toMonoidHom ≤ T := by
    rintro _ ⟨q, hq, rfl⟩
    exact hk ⟨q, hPT₂ (hQP hq), rfl⟩
  have hkM : k ∈ M := by
    rw [← hs.N_Q]
    exact mem_normalizer_of_map_conj_eq (hs.Q_wc k hQk)
  have hQ'k : Q.map (MulAut.conj (k * c * h⁻¹)).toMonoidHom ≤ T := by
    rintro _ ⟨q, hq, rfl⟩
    refine hk ⟨c * (h⁻¹ * q * h) * c⁻¹, hPT₂ (hc ⟨h⁻¹ * q * h, ⟨q, hq, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩, rfl⟩), ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hukM : k * c * h⁻¹ ∈ M := by
    rw [← hs.N_Q]
    exact mem_normalizer_of_map_conj_eq (hs.Q_wc _ hQ'k)
  refine ⟨(k * c * h⁻¹)⁻¹ * k, M.mul_mem (M.inv_mem hukM) hkM, ?_⟩
  have hcx : c * x * c⁻¹ = x := by
    have := Subgroup.mem_centralizer_singleton_iff.1 hcC
    calc c * x * c⁻¹ = (x * c) * c⁻¹ := by rw [this.symm]
      _ = x := by group
  calc h * x * h⁻¹ = h * (c⁻¹ * (c * x * c⁻¹) * c) * h⁻¹ := by group
    _ = h * (c⁻¹ * x * c) * h⁻¹ := by rw [hcx]
    _ = (k * c * h⁻¹)⁻¹ * k * x * ((k * c * h⁻¹)⁻¹ * k)⁻¹ := by group

theorem not_conj_mem_of_not_mem {L M T : Subgroup G} {n : ℕ} (hs : Sec6 G L M T n)
    {W : Subgroup G} (hWQ : W ≤ QOf L M) (hWM : ∀ m ∈ M, ∀ w ∈ W, m * w * m⁻¹ ∈ W)
    {x : G} (hx : x ∈ QOf L M) (hxW : x ∉ W) (h : G) : h * x * h⁻¹ ∉ W := by
  intro hW
  obtain ⟨m, hm, hmx⟩ := exists_conj_of_conj_mem_Q hs hx (hWQ hW)
  rw [hmx] at hW
  have := hWM m⁻¹ (M.inv_mem hm) _ hW
  apply hxW
  simpa [mul_assoc] using this

end CFSG.CGT.PushingUpLit.T2KR
