module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeSocDefs
public import CFSG.ClassicalInvolution.Q3.TA3SmallDefs
public import CFSG.Walter.W67.JR.OutPSL

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.GorensteinWalter (PSL2 IsOddPrimePower)
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ClassicalInvolution.Q3.TA3 (SmallL2)

theorem soc_l2_dihedral_mem_zpowers_r_one {m : ℕ} [NeZero m] {x : DihedralGroup m}
    (hx : 4 ≤ orderOf x) : x ∈ Subgroup.zpowers (DihedralGroup.r (1 : ZMod m)) := by
  cases x with
  | r i =>
    rw [Subgroup.mem_zpowers_iff]
    exact ⟨(i.val : ℤ), by rw [zpow_natCast, DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]⟩
  | sr i =>
    rw [DihedralGroup.orderOf_sr] at hx
    omega

theorem soc_l2_centralizer_mem_zpowers {G : Type} [Group G] {t : G} {m : ℕ} [NeZero m]
    (ψ : Subgroup.centralizer ({t} : Set G) ≃* DihedralGroup m)
    (c : Subgroup.centralizer ({t} : Set G)) (hc : ψ c = DihedralGroup.r (1 : ZMod m))
    {h : G} (hh : h ∈ Subgroup.centralizer ({t} : Set G)) (h4 : 4 ≤ orderOf h) :
    ∃ k : ℤ, (c : G) ^ k = h := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (soc_l2_dihedral_mem_zpowers_r_one
    (x := ψ ⟨h, hh⟩) (by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]; exact h4))
  have hxk : (⟨h, hh⟩ : Subgroup.centralizer ({t} : Set G)) = c ^ k := by
    apply ψ.injective
    rw [map_zpow, hc, hk]
  refine ⟨k, ?_⟩
  have h2 := congrArg Subtype.val hxk
  rw [Subgroup.coe_zpow] at h2
  exact h2.symm

theorem soc_l2_centralizer_dihedral (K : Type) [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    (hK : Nat.card K = p ^ f) (hp : Odd p) (hf : 0 < f) (h3 : 3 < p ^ f) {t : PSL2 K}
    (ht : orderOf t = 2) :
    ∃ m : ℕ, NeZero m ∧ Nonempty (Subgroup.centralizer ({t} : Set (PSL2 K)) ≃* DihedralGroup m) := by
  obtain ⟨h1, h3'⟩ := CFSG.Walter.psl2_centralizer_involution K hK hp hf ht
  have hodd : p ^ f % 2 = 1 := Nat.odd_iff.mp (hp.pow : Odd (p ^ f))
  rcases (by omega : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3) with h | h
  · exact ⟨(p ^ f - 1) / 2, ⟨by omega⟩, (h1 h).2⟩
  · exact ⟨(p ^ f + 1) / 2, ⟨by omega⟩, (h3' h).2⟩

theorem soc_l2_comm_of_cyclic_quot_central {G Q : Type} [Group G] [Group Q] [IsCyclic Q]
    (f : G →* Q) (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center G) (a b : G) :
    a * b = b * a := by
  obtain ⟨q, hq⟩ := IsCyclic.exists_generator (α := Q)
  obtain ⟨a0, rfl⟩ := hf q
  have key : ∀ x : G, ∃ z ∈ Subgroup.center G, ∃ k : ℤ, x = z * a0 ^ k := by
    intro x
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hq (f x))
    refine ⟨x * (a0 ^ k)⁻¹, hker ?_, k, by simp⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow, hk, mul_inv_cancel]
  obtain ⟨z1, hz1, k1, rfl⟩ := key a
  obtain ⟨z2, hz2, k2, rfl⟩ := key b
  have hcen : ∀ z : G, z ∈ Subgroup.center G → ∀ g : G, Commute g z :=
    fun z hz g => Subgroup.mem_center_iff.mp hz g
  have hc : Commute (a0 ^ k1) (a0 ^ k2) := (Commute.refl a0).zpow_zpow k1 k2
  have h : Commute (z1 * a0 ^ k1) (z2 * a0 ^ k2) :=
    Commute.mul_right (Commute.mul_left (hcen z1 hz1 z2).symm (hcen z2 hz2 (a0 ^ k1)))
      (Commute.mul_left (hcen z1 hz1 (a0 ^ k2)).symm hc)
  exact h.eq

theorem soc_l2_semilinearQuotient_comm (K : Type) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) : ∀ a b : SemilinearQuotient K, a * b = b * a := by
  haveI : IsCyclic (K ≃+* K) := fieldAut_isCyclic K
  have hdvd : Nat.card (quotientFieldProjection K).ker ∣ 2 := by
    rw [quotientFieldProjection_ker K]
    exact CFSG.Walter.W67.JROut.card_diagonalHom_range_dvd_two K hK
  exact soc_l2_comm_of_cyclic_quot_central (quotientFieldProjection K)
    (quotientFieldProjection_surjective K) (CFSG.Walter.W67.JROut.le_center_of_card_dvd_two hdvd)

theorem soc_l2_socleInvConj (K : Type) [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    (hK : Nat.card K = p ^ f) (hp : Odd p) (hf : 0 < f) {F : Type} [Group F]
    (e : F ≃* PSL2 K) : SocleInvConj F := by
  have hPSL : SocleInvConj (PSL2 K) := fun s t hs ht =>
    isConj_iff.mp (CFSG.Walter.psl2_isConj_of_orderOf_eq_two K hK hp hf hs ht)
  exact SocleInvConj.of_mulEquiv e hPSL

theorem soc_l2_socleCyc4 (K : Type) [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    (hK : Nat.card K = p ^ f) (hp : Odd p) (hf : 0 < f) (h3 : 3 < p ^ f)
    {F : Type} [Group F] [Finite F] (e : F ≃* PSL2 K) : SocleCyc4 F := by
  intro z hz N₁ N₂ P₁ P₂ hN₁ hN₂ _ _ hS₁ hS₂ hc₁ hc₂ hn₁ hn₂
  have ht : orderOf (e z) = 2 := by rw [MulEquiv.orderOf_eq]; exact hz
  obtain ⟨m, hm, ⟨ψ⟩⟩ := soc_l2_centralizer_dihedral K hK hp hf h3 ht
  haveI := hm
  obtain ⟨c, hc⟩ : ∃ c : Subgroup.centralizer ({e z} : Set (PSL2 K)),
      ψ c = DihedralGroup.r (1 : ZMod m) :=
    ⟨ψ.symm (DihedralGroup.r (1 : ZMod m)), ψ.apply_symm_apply _⟩
  have hA : ∀ P : Subgroup F, P ≤ Subgroup.centralizer ({z} : Set F) → IsCyclic P →
      4 ≤ Nat.card P → P ≤ Subgroup.zpowers (e.symm (c : PSL2 K)) := by
    intro P hPC hPcyc hPn
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := P)
    have hgo : orderOf (g : F) = Nat.card P := by rw [Subgroup.orderOf_coe, hg]
    have hgz : (g : F) * z = z * (g : F) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hPC g.2)
    have hhC : e (g : F) ∈ Subgroup.centralizer ({e z} : Set (PSL2 K)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h2 := congrArg e hgz
      rw [map_mul, map_mul] at h2
      exact h2
    have hh4 : 4 ≤ orderOf (e (g : F)) := by
      rw [MulEquiv.orderOf_eq, hgo]
      exact hPn
    obtain ⟨k, hk⟩ := soc_l2_centralizer_mem_zpowers ψ c hc hhC hh4
    have hgA : (g : F) ∈ Subgroup.zpowers (e.symm (c : PSL2 K)) := by
      have h2 : e.symm ((c : PSL2 K) ^ k) = (g : F) := by
        rw [hk, MulEquiv.symm_apply_apply]
      rw [map_zpow] at h2
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, h2⟩
    have htop : Subgroup.zpowers g = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hg])
    intro x hx
    have hxg : (⟨x, hx⟩ : P) ∈ Subgroup.zpowers g := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨k', hk'⟩ := Subgroup.mem_zpowers_iff.mp hxg
    have hx' : x = (g : F) ^ k' := by
      have h2 := congrArg Subtype.val hk'
      rw [Subgroup.coe_zpow] at h2
      exact h2.symm
    rw [hx']
    exact zpow_mem hgA k'
  exact soc_exists_common_orderOf_four (A := Subgroup.zpowers (e.symm (c : PSL2 K)))
    (Subgroup.isCyclic_zpowers _) (hA P₁ (hS₁.1.trans hN₁) hc₁ hn₁)
    (hA P₂ (hS₂.1.trans hN₂) hc₂ hn₂) hS₁.2.1 hS₂.2.1 hc₁ hc₂ hn₁ hn₂

theorem soc_l2_socleOutAbelian (K : Type) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (h3 : 3 < Nat.card K) {F : Type} [Group F]
    (e : F ≃* PSL2 K) : SocleOutAbelian F := by
  have hcomm : ∀ a b : Outer (PSL2 K), a * b = b * a := by
    intro a b
    apply (odd_outerEquivSemilinearQuotient K hK h3).symm.injective
    rw [map_mul, map_mul]
    exact soc_l2_semilinearQuotient_comm K hK _ _
  have hPSL : SocleOutAbelian (PSL2 K) := by
    intro P _
    exact ⟨⟨fun a b => Subtype.ext (hcomm a b)⟩⟩
  exact SocleOutAbelian.of_mulEquiv e hPSL

theorem soc_l2_data {F : Type} [Group F] (h : SmallL2 F) :
    ∃ (p f : ℕ) (K : Type) (_ : Field K) (_ : Finite K), p.Prime ∧ Odd p ∧ 0 < f ∧ 3 < p ^ f ∧
      Nat.card K = p ^ f ∧ Nonempty (F ≃* PSL2 K) := by
  obtain ⟨p, f, hp, hp2, hf, hadm, K, instF, instFin, hK, ⟨e⟩⟩ := h
  have h23 : p ^ f ≠ 3 := by
    obtain ⟨-, -, -, -, h23⟩ := hadm
    intro h3
    exact h23 (by rw [h3])
  have hpf : p ^ 1 ≤ p ^ f := Nat.pow_le_pow_right hp.pos (by omega)
  rw [pow_one] at hpf
  have hp3 : 2 ≤ p := hp.two_le
  refine ⟨p, f, K, instF, instFin, hp, hp.odd_of_ne_two hp2, by omega, by omega, hK, ⟨?_⟩⟩
  exact ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).trans
    e.symm).symm

theorem socleInvConj_l2 {F : Type} [Group F] [Finite F] (h : SmallL2 F) : SocleInvConj F := by
  obtain ⟨p, f, K, _, _, hp, hpodd, hf, -, hK, ⟨e⟩⟩ := soc_l2_data h
  haveI : Fact p.Prime := ⟨hp⟩
  exact soc_l2_socleInvConj K hK hpodd hf e

theorem socleCyc4_l2 {F : Type} [Group F] [Finite F] (h : SmallL2 F) : SocleCyc4 F := by
  obtain ⟨p, f, K, _, _, hp, hpodd, hf, h3, hK, ⟨e⟩⟩ := soc_l2_data h
  haveI : Fact p.Prime := ⟨hp⟩
  exact soc_l2_socleCyc4 K hK hpodd hf h3 e

theorem socleOutAbelian_l2 {F : Type} [Group F] [Finite F] (h : SmallL2 F) :
    SocleOutAbelian F := by
  obtain ⟨p, f, K, _, _, hp, hpodd, hf, h3, hK, ⟨e⟩⟩ := soc_l2_data h
  exact soc_l2_socleOutAbelian K ⟨p, f, hp, hpodd, by omega, hK⟩ (by rw [hK]; exact h3) e

theorem socleFactsR_l2 {F : Type} [Group F] [Finite F] (h : SmallL2 F) : SocleFactsR F :=
  SocleFactsR.of_parts (socleInvConj_l2 h) (socleCyc4_l2 h) (socleOutAbelian_l2 h)

end CFSG.CGT.PushingUpLit.SolKNA.R4
