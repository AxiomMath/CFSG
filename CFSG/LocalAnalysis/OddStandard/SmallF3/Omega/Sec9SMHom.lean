module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SME1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SMAut
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SMGrp
import CFSG.GroupTheory.ElemAbelianClosure

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec9m_exists_commHom {M B : Subgroup G} {a : G}
    (hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b)
    (hMB : ∀ m ∈ M, ∀ b ∈ B, m * b = b * m) (ha : ∀ m ∈ M, m * a * m⁻¹ * a⁻¹ ∈ B) :
    ∃ f : ↥M →* ↥B, ∀ m : ↥M, ((f m : ↥B) : G) = (m : G) * a * (m : G)⁻¹ * a⁻¹ := by
  refine ⟨MonoidHom.mk' (fun m : ↥M =>
    (⟨(m : G) * a * (m : G)⁻¹ * a⁻¹, ha m m.2⟩ : ↥B)) ?_, fun m => rfl⟩
  intro x y
  apply Subtype.ext
  change (x : G) * (y : G) * a * ((x : G) * (y : G))⁻¹ * a⁻¹ =
    ((x : G) * a * (x : G)⁻¹ * a⁻¹) * ((y : G) * a * (y : G)⁻¹ * a⁻¹)
  have hxy : (y : G) * a * (y : G)⁻¹ * a⁻¹ ∈ B := ha y y.2
  have hxcomm : (x : G) * ((y : G) * a * (y : G)⁻¹ * a⁻¹) =
      ((y : G) * a * (y : G)⁻¹ * a⁻¹) * (x : G) := hMB x x.2 _ hxy
  rw [show (x : G) * (y : G) * a * ((x : G) * (y : G))⁻¹ * a⁻¹ =
      (x : G) * ((y : G) * a * (y : G)⁻¹ * a⁻¹) * (x : G)⁻¹ *
        ((x : G) * a * (x : G)⁻¹ * a⁻¹) by group]
  rw [show (x : G) * ((y : G) * a * (y : G)⁻¹ * a⁻¹) * (x : G)⁻¹ =
      (y : G) * a * (y : G)⁻¹ * a⁻¹ by rw [hxcomm]; group]
  exact hBc ((y : G) * a * (y : G)⁻¹ * a⁻¹) hxy ((x : G) * a * (x : G)⁻¹ * a⁻¹)
    (ha x x.2)

theorem sec9m_conj_comm {B : Subgroup G} {a m n : G}
    (hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) (hna : n⁻¹ * a * n * a⁻¹ ∈ B)
    (hmB : ∀ b ∈ B, m * b = b * m) (hma : m * a * m⁻¹ * a⁻¹ ∈ B) :
    (n * m * n⁻¹) * a * (n * m * n⁻¹)⁻¹ * a⁻¹ = n * (m * a * m⁻¹ * a⁻¹) * n⁻¹ := by
  have h1 : (n * m * n⁻¹) * a * (n * m * n⁻¹)⁻¹ * a⁻¹ =
      n * (m * (n⁻¹ * a * n) * m⁻¹ * (n⁻¹ * a * n)⁻¹) * n⁻¹ := by group
  have hcan : n⁻¹ * a * n = (n⁻¹ * a * n * a⁻¹) * a := by group
  have hmc : m * (n⁻¹ * a * n * a⁻¹) * m⁻¹ = n⁻¹ * a * n * a⁻¹ := by
    rw [hmB _ hna, mul_assoc, mul_inv_cancel, mul_one]
  have hmid : m * ((n⁻¹ * a * n * a⁻¹) * a) * m⁻¹ * ((n⁻¹ * a * n * a⁻¹) * a)⁻¹ =
      m * a * m⁻¹ * a⁻¹ := by
    calc m * ((n⁻¹ * a * n * a⁻¹) * a) * m⁻¹ * ((n⁻¹ * a * n * a⁻¹) * a)⁻¹
        = (m * (n⁻¹ * a * n * a⁻¹) * m⁻¹) * (m * a * m⁻¹) * a⁻¹ *
            (n⁻¹ * a * n * a⁻¹)⁻¹ := by group
      _ = (n⁻¹ * a * n * a⁻¹) * (m * a * m⁻¹) * a⁻¹ * (n⁻¹ * a * n * a⁻¹)⁻¹ := by
            rw [hmc]
      _ = (n⁻¹ * a * n * a⁻¹) * (m * a * m⁻¹ * a⁻¹) * (n⁻¹ * a * n * a⁻¹)⁻¹ := by group
      _ = m * a * m⁻¹ * a⁻¹ := by
            rw [hBc (n⁻¹ * a * n * a⁻¹) hna (m * a * m⁻¹ * a⁻¹) hma]
            group
  rw [h1, hcan, hmid]

variable [Finite G] {t t₀ z g : G} {L S B E1 : Subgroup G}

theorem sec9m_exists_W (hctx : Sec9E1 G t L S z g B t₀ E1)
    (hMB : ∀ m ∈ E1 ⊔ oddCoreIn (centMod (Asub9 t t₀ B) B), ∀ b ∈ B, m * b = b * m)
    (hOA : ∀ o ∈ oddCoreIn (centMod (Asub9 t t₀ B) B), ∀ a ∈ Asub9 t t₀ B, o * a = a * o) :
    ∃ W : Subgroup (↥B × ↥B), Nat.card W ≤ 16 ∧
      (∀ h ∈ autIn (centMod (Asub9 t t₀ B) B) B, ∀ w ∈ W, (h w.1, h w.2) ∈ W) ∧
      ∀ m ∈ E1 ⊔ oddCoreIn (centMod (Asub9 t t₀ B) B), ∃ w ∈ W,
        ((w.1 : ↥B) : G) = m * t * m⁻¹ * t⁻¹ ∧ ((w.2 : ↥B) : G) = m * t₀ * m⁻¹ * t₀⁻¹ := by
  have hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b :=
    fun b hb b' hb' => CFSG.Open.IsElemAbelian.comm hctx.choice.B_e16.1 hb hb'
  have htA : t ∈ Asub9 t t₀ B := by
    rw [Asub9]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
  have ht0A : t₀ ∈ Asub9 t t₀ B := by
    rw [Asub9]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers t₀))
  have hO_le_N : oddCoreIn (centMod (Asub9 t t₀ B) B) ≤ centMod (Asub9 t t₀ B) B :=
    (oddCoreIn_normal _).1
  have hM_le_N : E1 ⊔ oddCoreIn (centMod (Asub9 t t₀ B) B) ≤ centMod (Asub9 t t₀ B) B :=
    sup_le hctx.le_N hO_le_N
  have htB : ∀ m ∈ E1 ⊔ oddCoreIn (centMod (Asub9 t t₀ B) B), m * t * m⁻¹ * t⁻¹ ∈ B :=
    fun m hm => (hM_le_N hm).2 t htA
  have ht0B : ∀ m ∈ E1 ⊔ oddCoreIn (centMod (Asub9 t t₀ B) B),
      m * t₀ * m⁻¹ * t₀⁻¹ ∈ B := fun m hm => (hM_le_N hm).2 t₀ ht0A
  obtain ⟨ft, hft⟩ := sec9m_exists_commHom (M := E1 ⊔ oddCoreIn (centMod (Asub9 t t₀ B) B))
    (B := B) (a := t) hBc hMB htB
  obtain ⟨ft0, hft0⟩ := sec9m_exists_commHom (M := E1 ⊔ oddCoreIn (centMod (Asub9 t t₀ B) B))
    (B := B) (a := t₀) hBc hMB ht0B
  let c : ↥(E1 ⊔ oddCoreIn (centMod (Asub9 t t₀ B) B)) →* ↥B × ↥B := ft.prod ft0
  obtain ⟨ψ, hψ, hker⟩ := hctx.quot
  refine ⟨c.range, ?_, ?_, ?_⟩
  · have hcard : Nat.card c.range ≤ Nat.card E16 := by
      apply sec9m_card_range_le_sup (M := E1 ⊔ oddCoreIn (centMod (Asub9 t t₀ B) B))
        (E := E1) (O := oddCoreIn (centMod (Asub9 t t₀ B) B))
        le_sup_left le_sup_right le_rfl c ?_ ψ hψ ?_
      · intro o ho
        have h1 : ft o = 1 := by
          apply Subtype.ext
          rw [hft o]
          change (o : G) * t * (o : G)⁻¹ * t⁻¹ = 1
          rw [hOA (o : G) ho t htA]
          group
        have h2 : ft0 o = 1 := by
          apply Subtype.ext
          rw [hft0 o]
          change (o : G) * t₀ * (o : G)⁻¹ * t₀⁻¹ = 1
          rw [hOA (o : G) ho t₀ ht0A]
          group
        show (ft o, ft0 o) = (1, 1)
        rw [h1, h2]
      · intro e he heM
        have heA : (e : G) ∈ Asub9 t t₀ B := by
          have hmem : e ∈ ψ.ker := MonoidHom.mem_ker.mpr he
          rw [hker] at hmem
          exact Subgroup.mem_subgroupOf.mp hmem
        have hAel : CFSG.Open.IsElemAbelian 2 (Asub9 t t₀ B) :=
          sec9n_A_elem hctx.choice.toSec9Ctx
        have h1 : ft ⟨e, heM⟩ = 1 := by
          apply Subtype.ext
          rw [hft ⟨e, heM⟩]
          change (e : G) * t * (e : G)⁻¹ * t⁻¹ = 1
          rw [hAel.comm heA htA]
          group
        have h2 : ft0 ⟨e, heM⟩ = 1 := by
          apply Subtype.ext
          rw [hft0 ⟨e, heM⟩]
          change (e : G) * t₀ * (e : G)⁻¹ * t₀⁻¹ = 1
          rw [hAel.comm heA ht0A]
          group
        show (ft ⟨e, heM⟩, ft0 ⟨e, heM⟩) = (1, 1)
        rw [h1, h2]
    rw [sec9m_card_E16] at hcard
    exact hcard
  · intro h hh w hw
    obtain ⟨n, hnN, _hnB, hnconj⟩ := sec9m_mem_autIn.mp hh
    obtain ⟨m0, hm0⟩ := MonoidHom.mem_range.mp hw
    have hmemM : n * (m0 : G) * n⁻¹ ∈ E1 ⊔ oddCoreIn (centMod (Asub9 t t₀ B) B) :=
      (Subgroup.normal_subgroupOf_iff hM_le_N).mp hctx.normal (m0 : G) n m0.2 hnN
    let m' : ↥(E1 ⊔ oddCoreIn (centMod (Asub9 t t₀ B) B)) :=
      ⟨n * (m0 : G) * n⁻¹, hmemM⟩
    have hninv : n⁻¹ ∈ centMod (Asub9 t t₀ B) B := inv_mem hnN
    have hna_t : n⁻¹ * t * n * t⁻¹ ∈ B := by simpa using hninv.2 t htA
    have hna_t0 : n⁻¹ * t₀ * n * t₀⁻¹ ∈ B := by simpa using hninv.2 t₀ ht0A
    have hft_eq : ft m' = h (ft m0) := by
      apply Subtype.ext
      rw [hft m', hnconj (ft m0), hft m0]
      exact sec9m_conj_comm hBc hna_t (hMB (m0 : G) m0.2) ((hM_le_N m0.2).2 t htA)
    have hft0_eq : ft0 m' = h (ft0 m0) := by
      apply Subtype.ext
      rw [hft0 m', hnconj (ft0 m0), hft0 m0]
      exact sec9m_conj_comm hBc hna_t0 (hMB (m0 : G) m0.2) ((hM_le_N m0.2).2 t₀ ht0A)
    have hcm' : c m' = (h w.1, h w.2) := by
      rw [← hm0]
      show (ft m', ft0 m') = (h (ft m0), h (ft0 m0))
      rw [hft_eq, hft0_eq]
    exact MonoidHom.mem_range.mpr ⟨m', hcm'⟩
  · intro m hm
    refine ⟨c ⟨m, hm⟩, MonoidHom.mem_range.mpr ⟨⟨m, hm⟩, rfl⟩, hft ⟨m, hm⟩, hft0 ⟨m, hm⟩⟩

end CFSG.OddStandard.SmallF3.Omega
