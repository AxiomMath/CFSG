module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf5Trans

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

namespace TwinThmEW

section Lift

variable {G : Type} [Group G] [Finite G] {N : Subgroup G} [N.Normal]

theorem le_sup_of_map_eq {V R : Subgroup G} (h : V.map (QuotientGroup.mk' N) = R.map (QuotientGroup.mk' N)) :
    V ≤ R ⊔ N := by
  intro x hx
  have : QuotientGroup.mk' N x ∈ R.map (QuotientGroup.mk' N) := h ▸ Subgroup.mem_map_of_mem _ hx
  have h2 := (Subgroup.mem_comap).mpr this
  rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h2

theorem isSylow2In_sup_odd' (hN : Odd (Nat.card N)) {M R : Subgroup G} (hR : IsSylow2In R M) :
    IsSylow2In R (M ⊔ N) := by
  have hRN : IsSylow2In R (R ⊔ N) := TwinPerpV3.isSylow2In_sup_of_odd hN hR.2.1
  have hRb := isSylow2In_map_mk hN hR
  refine ⟨hR.1.trans le_sup_left, hR.2.1, fun V hVle hV2 hRV => ?_⟩
  have hNmap : N.map (QuotientGroup.mk' N) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨x, hx, rfl⟩
    simpa using hx
  have hVM : V.map (QuotientGroup.mk' N) ≤ M.map (QuotientGroup.mk' N) := by
    have := Subgroup.map_mono (f := QuotientGroup.mk' N) hVle
    rwa [Subgroup.map_sup, hNmap, sup_bot_eq] at this
  have hVeq : V.map (QuotientGroup.mk' N) = R.map (QuotientGroup.mk' N) :=
    hRb.2.2 _ hVM (hV2.map _) (Subgroup.map_mono hRV)
  exact hRN.2.2 V (le_sup_of_map_eq hVeq) hV2 hRV

theorem exists_conj_le_of_le_sup (hN : Odd (Nat.card N)) {M P : Subgroup G} (hP : IsPGroup 2 P)
    (hPM : P ≤ M ⊔ N) : ∃ n ∈ N, conjSub n P ≤ M := by
  obtain ⟨R₀, hR₀, -⟩ := IsSylow2In.exists_ge (T := ⊥) (P := M) IsPGroup.of_bot bot_le
  have hY := isSylow2In_sup_odd' hN hR₀
  obtain ⟨Q, hQ, hPQ⟩ := IsSylow2In.exists_ge hP hPM
  obtain ⟨x, hx, hxQ⟩ := Asc77.exists_conjSub_eq_of_isSylow2In hY hQ
  obtain ⟨m, hm, n, hn, hmn⟩ := Subgroup.mem_sup_of_normal_right.mp hx
  have hn' : m * n * m⁻¹ ∈ N := ‹N.Normal›.conj_mem n hn m
  have hxe : x = (m * n * m⁻¹) * m := by rw [← hmn]; group
  have hR'' : conjSub m R₀ ≤ M := by
    have := conjSub_mono (n := m) hR₀.1
    rwa [conjSub_eq_self_of_mem hm] at this
  have hQle : Q ≤ conjSub (m * n * m⁻¹) M := by
    rw [← hxQ, hxe, conjSub_mul]
    exact conjSub_mono hR''
  refine ⟨(m * n * m⁻¹)⁻¹, N.inv_mem hn', ?_⟩
  rw [conjSub_le_iff, inv_inv]
  exact hPQ.trans hQle

theorem le_sup_of_map_le {V R : Subgroup G}
    (h : V.map (QuotientGroup.mk' N) ≤ R.map (QuotientGroup.mk' N)) : V ≤ R ⊔ N := by
  intro x hx
  have : QuotientGroup.mk' N x ∈ R.map (QuotientGroup.mk' N) := h (Subgroup.mem_map_of_mem _ hx)
  have h2 := (Subgroup.mem_comap).mpr this
  rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h2

end Lift

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
