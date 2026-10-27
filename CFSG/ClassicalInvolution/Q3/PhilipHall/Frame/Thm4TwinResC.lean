module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinTight
public import CFSG.ClassicalInvolution.Q3.TL3T26

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC.Thin

namespace Thm4Twin

theorem thm4TwinRes2CDTw_of_d1Gen {n : ℕ} (hD : ThmD1GenBelow 3 n) : Thm4TwinRes2CDTw 3 n := by
  intro G _ _ hG J L hm hgen _ u v hu hv hinu hinv _ _
  have h := hm.hyp
  obtain ⟨Pu, hPun, hPu2, huP⟩ := hinu
  obtain ⟨Pv, hPvn, hPv2, hvP⟩ := hinv
  have : Pv.Normal := hPvn
  have : Pu.Normal := hPun
  have hQn : (Pu ⊔ Pv).Normal := Subgroup.sup_normal Pu Pv
  have hQ2 : IsPGroup 2 ↥(Pu ⊔ Pv) := IsPGroup.to_sup_of_normal_right hPu2 hPv2
  have huQ : u ∈ Pu ⊔ Pv := Subgroup.mem_sup_left huP
  have hvQ : v ∈ Pu ⊔ Pv := Subgroup.mem_sup_right hvP
  have hinv' : ∀ K ∈ CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L, ∀ z : G,
      IsUniqueInvolution K z → z ∈ Pu ⊔ Pv := by
    rintro K (⟨g, rfl⟩ | ⟨g, rfl⟩) z hz
    · rw [hz.eq (hu.conj g)]; exact hQn.conj_mem u huQ g
    · rw [hz.eq (hv.conj g)]; exact hQn.conj_mem v hvQ g
  have h2 : ∀ K ∈ CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L, IsPGroup 2 K := by
    intro K hK
    obtain ⟨z, hz⟩ := (h.hyp.omega1 K hK).1
    exact h.isPGroup_of_inO2 hK hz ⟨_, hQn, hQ2, hinv' K hK z hz⟩
  have h8 : ∀ K ∈ CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L, Nat.card K = 2 ^ 3 := by
    intro K hK
    have hKS : IsSylow2In K K := ⟨le_rfl, h2 K hK, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
    obtain ⟨e⟩ := h.quat K hK K hKS
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    norm_num
  have hlt : Nat.card ↥(pSpan (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L)) < n :=
    lt_of_le_of_lt (Subgroup.card_le_card_group _) hG
  have hc := hD G _ h.hyp h2 h8 h.aEmpty _ subset_rfl hlt
    (fun K hK x _ => h.hyp.conjInvariant x K hK)
    (TL4.oddCore_eq_bot_of_normal h.odd (omegaGen_normal h.hyp.conjInvariant))
    (fun K hK z hz => ⟨Pu ⊔ Pv, le_of_eq_of_le rfl (by rw [show pSpan _ = ⊤ from hgen]; exact le_top),
      fun x _ q hq => hQn.conj_mem q hq x, hQ2, hinv' K hK z hz⟩)
    J hm.memJ L hm.memL (fun ⟨x, _, hx⟩ => hm.notConj ⟨x, hx⟩)
  exact hm.notComm hc

end Thm4Twin
end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
