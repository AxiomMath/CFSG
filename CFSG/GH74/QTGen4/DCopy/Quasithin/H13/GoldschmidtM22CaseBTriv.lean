module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22CaseBSetup
public import CFSG.Quasithin.H13.GoldschmidtM22CaseBComm
public section
namespace CFSG.Quasithin.H13.GM22
open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin
variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]
namespace BCtx_F4
variable {T M L V : Subgroup G} {g : G} {D : Subgroup G} (c : BCtx_F4 T M L V g D)
include c in
theorem N_eq_mul : ∀ n ∈ Subgroup.normalizer (V : Set G),
    ∃ x ∈ actTriv V, ∃ q ∈ Subgroup.centralizer (V : Set G), n = x * q := by
  obtain ⟨a, haD, haN, has, ha2⟩ := c.exists_odd
  have haA : a ∈ actTriv V := ⟨haN, fun q hq => c.D_comm_Q haD hq⟩
  have haa : c.ρ a * c.ρ a = 1 := by
    rw [← PermRho.apply_mul haN haN, ← pow_two, ha2, PermRho.apply_one]
  exact c.ρ.exists_mul_of_actTriv haA haa has
include c in
theorem L_comm_Q : ∀ l ∈ L, ∀ q ∈ Subgroup.centralizer (V : Set G), l * q * l⁻¹ * q⁻¹ ∈ V :=
  fun _ hl q hq =>
    (le_actTriv c.L_le_N c.L_perfect c.Q_two c.N_eq_mul hl).2 q hq
include c in
theorem CT_L : ∀ x ∈ T, (∀ l ∈ L, l * x = x * l) → x = 1 := by
  intro x hxT hx
  have h1 := (c.hl.h616 G T M L V 2 c.h.toHyp611).1.2
  have : x ∈ T ⊓ Subgroup.centralizer (L : Set G) :=
    ⟨hxT, Subgroup.mem_centralizer_iff.mpr hx⟩
  rw [h1] at this
  exact Subgroup.mem_bot.mp this
include c in
theorem isElemAbelian_Q : IsElemAbelian 2 (Subgroup.centralizer (V : Set G)) :=
  isElemAbelian_centralizer c.h.toHyp611.isElemAbelian c.Q_le_T c.CT_L c.L_comm_Q
include c in
theorem Q_comm {x y : G} (hx : x ∈ Subgroup.centralizer (V : Set G))
    (hy : y ∈ Subgroup.centralizer (V : Set G)) : x * y = y * x :=
  congrArg Subtype.val (c.isElemAbelian_Q.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
include c in
theorem N_comm_Q : ∀ n ∈ Subgroup.normalizer (V : Set G), ∀ q ∈ Subgroup.centralizer (V : Set G),
    n * q * n⁻¹ * q⁻¹ ∈ V := by
  intro n hn q hq
  obtain ⟨x, hx, q', hq', rfl⟩ := c.N_eq_mul n hn
  have h1 := hx.2 q hq
  have h2 : x * q' * q * (x * q')⁻¹ * q⁻¹ = x * q * x⁻¹ * q⁻¹ := by
    calc x * q' * q * (x * q')⁻¹ * q⁻¹ = x * (q' * q) * q'⁻¹ * x⁻¹ * q⁻¹ := by group
      _ = x * (q * q') * q'⁻¹ * x⁻¹ * q⁻¹ := by rw [c.Q_comm hq' hq]
      _ = x * q * x⁻¹ * q⁻¹ := by group
  rw [h2]
  exact h1
end BCtx_F4
end CFSG.Quasithin.H13.GM22
