module

public import CFSG.GF2Type.Smith1979.IdxFourHSyl
public import CFSG.GF2Type.Smith1979.IdxFourHInner
public import CFSG.GF2Type.Smith1979.IdxFourHTwo
public import CFSG.LargeExtraspecial.S14C12TOrd
public import CFSG.GF2Type.Smith1979.IdxFourHX

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.IdxFour

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem K_normal {K : Subgroup S.O} (hK : K ≤ S.Mbar) (hidx : K.relIndex S.Mbar = 2) :
    ∀ m ∈ S.Mbar, ∀ k ∈ K, m * k * m⁻¹ ∈ K := by
  intro m hm k hk
  have hN : (K.subgroupOf S.Mbar).Normal := Subgroup.normal_of_index_eq_two hidx
  have := hN.conj_mem ⟨k, hK hk⟩ (mem_subgroupOf.mpr hk) ⟨m, hm⟩
  simpa [mem_subgroupOf] using this

theorem conj_mem_QG_of_mem_L0 {g x : G} (hx : x ∈ S.L0 g) : g⁻¹ * x * g ∈ S.QG := by
  have hx' : x ∈ S.Qa g := hx.1
  rw [S.Qa_eq_map] at hx'
  obtain ⟨y, hy, rfl⟩ := hx'
  have e : g⁻¹ * ((MulAut.conj g).toMonoidHom y) * g = y := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [e]
  exact hy

theorem exists_conj_mem_QG {g : G} (H : S4.Hyp4 S g) (C : S4.Cons311 S g) {K : Subgroup S.O}
    {θ xb : S.O} (hF : IdxFourFacts S g K θ xb) {l : G} (hl : l ∈ pre S K) (hll : l * l = 1) :
    ∃ h : G, h * l * h⁻¹ ∈ S.QG := by
  by_cases hlQ : l ∈ S.QG
  · exact ⟨1, by simpa using hlQ⟩
  have hlM : l ∈ S.M := pre_le_M K hl
  set lb : S.O := S.ρ ⟨l, hlM⟩ with hlb
  have hlbK : lb ∈ K := rho_mem_of_mem_pre hl hlM
  have hlb1 : lb ≠ 1 := fun h => hlQ ((S.ρ_eq_one_iff ⟨l, hlM⟩).mp h)
  have hlb2 : lb * lb = 1 := by
    have : (⟨l, hlM⟩ : S.M) * ⟨l, hlM⟩ = 1 := Subtype.ext hll
    rw [hlb, ← map_mul, this, map_one]
  obtain ⟨m, hmM, hm⟩ := hF.inv_conj lb hlbK hlb1 hlb2
  obtain ⟨m₁, rfl⟩ := MonoidHom.mem_range.mp hmM
  set t : S.O := S.ρ m₁ * lb * (S.ρ m₁)⁻¹ with ht
  have ht1 : t ≠ 1 := by
    intro h
    apply hlb1
    have : lb = (S.ρ m₁)⁻¹ * t * S.ρ m₁ := by rw [ht]; group
    rw [this, h]
    group
  have hl₁M : (m₁ : G) * l * (m₁ : G)⁻¹ ∈ S.M :=
    S.M.mul_mem (S.M.mul_mem m₁.2 hlM) (S.M.inv_mem m₁.2)
  have hl₁l₁ : ((m₁ : G) * l * (m₁ : G)⁻¹) * ((m₁ : G) * l * (m₁ : G)⁻¹) = 1 := by
    calc ((m₁ : G) * l * (m₁ : G)⁻¹) * ((m₁ : G) * l * (m₁ : G)⁻¹)
        = (m₁ : G) * (l * l) * (m₁ : G)⁻¹ := by group
      _ = 1 := by rw [hll]; group
  have hl₁ρ : S.ρ ⟨(m₁ : G) * l * (m₁ : G)⁻¹, hl₁M⟩ = t := by
    have : (⟨(m₁ : G) * l * (m₁ : G)⁻¹, hl₁M⟩ : S.M) = m₁ * ⟨l, hlM⟩ * m₁⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv]
  have hfuse : ∃ y ∈ S.M, y * ((m₁ : G) * l * (m₁ : G)⁻¹) * y⁻¹ ∈ S.L0 g := by
    rcases hF.lbar t hm ht1 with hout | hin
    · obtain ⟨q, hq, hql⟩ := outer_fusion H C hm ht1 hout hl₁M hl₁l₁ hl₁ρ
      exact ⟨q, S.QG_le_M hq, hql⟩
    · exact inner_fusion H C hF.θ_mem hF.θ_cube hF.θ_fpf hm ht1 hin hl₁M hl₁l₁ hl₁ρ
  obtain ⟨y, -, hy⟩ := hfuse
  refine ⟨g⁻¹ * y * m₁, ?_⟩
  have h1 := conj_mem_QG_of_mem_L0 hy
  have e : (g⁻¹ * y * (m₁ : G)) * l * (g⁻¹ * y * (m₁ : G))⁻¹ =
      g⁻¹ * (y * ((m₁ : G) * l * (m₁ : G)⁻¹) * y⁻¹) * g := by group
  rw [e]
  exact h1

theorem false_of_idx4 [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hTI : WeaklyClosedTITransitive.{0}) (S : Setting G) (hw : S.width = 6)
    (hirr : ¬ S.IsReducible) (hnoAll : S11.NoA2All S) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) {K : Subgroup S.O} {θ xb : S.O}
    (hF : IdxFourFacts S g K θ xb) : False := by
  have hno := hnoAll g haQ hne
  have H := S14.hyp4_of hTI (by omega) haQ hne hno hirr
  have C := S14.cons311_of hTI (by omega) haQ hne hno hirr
  obtain ⟨x, hxM, hxx, hρx, U, hU9, hUF, hUc, hUW⟩ := exists_x_data hF hw
  obtain ⟨T, hT, hTcard⟩ :=
    exists_sylow_centralizer S hTI hw hirr hnoAll hF hxM hxx hρx hU9 hUF hUc hUW
  have hxK : x ∉ pre S K := fun h => hF.x_not_mem (hρx ▸ rho_mem_of_mem_pre h hxM)
  have hx1 : x ≠ 1 := fun h => hxK (h ▸ (pre S K).one_mem)
  have hx2 : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hxx) hx1
  have hodd : Nat.Coprime 2 S.M.index :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (S14.not_two_dvd_index_M S)
  refine false_of_conj_not_mem hnonab hodd (pre_le_M K)
    (fun h hh k hk => conj_mem_pre (K_normal hF.K_le hF.K_index) hh hk)
    (pre_relIndex hF.K_le hF.K_index) hxM hxK hx2 ?_
  intro a haM haK
  set l : G := a⁻¹ * x * a with hl
  have hll : l * l = 1 := by
    calc l * l = a⁻¹ * (x * x) * a := by rw [hl]; group
      _ = 1 := by rw [hxx]; group
  obtain ⟨h, hh⟩ := exists_conj_mem_QG H C hF haK hll
  set j : G := h * l * h⁻¹ with hj
  have hjj : j * j = 1 := by
    calc j * j = h * (l * l) * h⁻¹ := by rw [hj]; group
      _ = 1 := by rw [hll]; group
  have hj1 : j ≠ 1 := by
    intro h1
    apply hx1
    have : x = a * (h⁻¹ * j * h) * a⁻¹ := by rw [hj, hl]; group
    rw [this, h1]
    group
  obtain ⟨P, hPj, hP2, hPcard⟩ := exists_two_subgroup_centralizer hw hF.stab_two
    (S4.cl_conj_z_ne_zero S haQ hne) (S4.q_cl_conj_z S haQ) hh hjj hj1
  have hjx : j = (h * a⁻¹) * x * (h * a⁻¹)⁻¹ := by rw [hj, hl]; group
  have hP' : P ≤ centralizer ({(h * a⁻¹) * x * (h * a⁻¹)⁻¹} : Set G) := by rw [← hjx]; exact hPj
  have := card_le_of_isSylowTwoIn hT hP2 hP'
  omega

end CFSG.GF2Type.Smith1979.IdxFour
