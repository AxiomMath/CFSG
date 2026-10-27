module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Elementary
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.NotationAPI

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

theorem lemma2511 : Lemma2511 := by
  intro G _ _ T M hs N h
  have hS : N.S ≤ T := N.S_le_T
  have hS2 : IsPGroup 2 N.S := N.tuple.sylow.isPGroup
  have hxN : N.x ∈ Subgroup.normalizer (N.S : Set G) := N.x_mem.2
  have hxT : N.x ∈ T := N.x_mem.1
  have hz2 : N.z * N.z = 1 := by have := N.tuple.z_sq; rwa [sq] at this
  have hz1 : N.z ≠ 1 := N.tuple.z_ne_one
  have hzT : N.z ∈ centerOf T := N.tuple.z_mem
  have hzSS : N.z ∈ centerOf N.S :=
    ⟨N.tuple.center_le hzT, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hS) hzT.2⟩
  have hzSC : N.z ∉ N.SC := h.facts254.z_not_mem
  obtain ⟨zK, hzK0, hzKproj, hZSK0, hzKcard⟩ := h.facts258.zK_exists
  have hzKZ : zK ∈ centerOf N.S := by
    have : zK ∈ centerOf N.S ⊓ N.SK0 := by rw [hZSK0]; exact Subgroup.mem_zpowers zK
    exact this.1
  have hzK2 : zK * zK = 1 := by
    have h1 : orderOf zK = 2 := by rw [← Nat.card_zpowers]; exact hzKcard
    have := pow_orderOf_eq_one zK
    rwa [h1, sq] at this
  have hdec : centerOf N.S = Subgroup.zpowers zK ⊔ (centerOf N.S ⊓ N.SC) := by
    have := h.facts258.center_decomp
    rwa [hZSK0] at this
  obtain ⟨t, htSC, ht1, ht2, htZ, hZt⟩ := exists_involution_center_decomp hS2 N.SC_le_S
    N.S_le_normalizer_SC h.facts254.SC_ne_bot hxN h.concl255.1 hzK2 hzKZ hdec
  have htcS : ∀ s ∈ N.S, s * t = t * s := fun s hs' => Subgroup.mem_centralizer_iff.mp htZ.2 s hs'
  have htK0 : ∀ k ∈ N.K0, k * t = t * k := fun k hk =>
    Subgroup.mem_centralizer_iff.mp (N.SC_le_centralizer htSC) k hk
  have hcomm : t * zK = zK * t := (Subgroup.mem_centralizer_iff.mp htZ.2 zK hzKZ.1).symm
  have hcommz : t * N.z = N.z * t := Subgroup.mem_centralizer_iff.mp hzSS.2 t htZ.1
  have htxC : N.x⁻¹ * t * N.x ∈ CFSG.conjugate N.SC N.x := by
    rw [mem_conjugate_iff]
    have e : N.x * (N.x⁻¹ * t * N.x) * N.x⁻¹ = t := by group
    rw [e]; exact htSC
  have hxt : N.x⁻¹ * t * N.x ≠ t := by
    intro heq
    have hmem : t ∈ N.SC ⊓ CFSG.conjugate N.SC N.x := ⟨htSC, by rw [← heq]; exact htxC⟩
    rw [h.concl255.1, Subgroup.mem_bot] at hmem
    exact ht1 hmem
  have hx1 : N.x⁻¹ * t * N.x ≠ 1 := by
    intro h1
    apply ht1
    calc t = N.x * (N.x⁻¹ * t * N.x) * N.x⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hzK1 : zK ≠ 1 := by
    intro h1
    refine hzSC ?_
    have := hzKproj
    rwa [h1, inv_one, one_mul] at this
  have hzKt : zK ≠ t := by
    intro h1
    apply ht1
    have hK0 : t ∈ N.K0 := by rw [← h1]; exact hzK0
    have hmem : t ∈ N.K0 ⊓ N.SC := ⟨hK0, htSC⟩
    rw [h.facts258.K0_inf_SC] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hzt : N.z ≠ t := by
    intro h1
    apply hzSC
    rw [h1]; exact htSC
  have hconjZ : N.x⁻¹ * t * N.x ∈ centerOf N.S := inv_conj_mem_centerOf hxN htZ
  have centerS_x : centerOf N.S = Subgroup.closure ({t, N.x⁻¹ * t * N.x} : Set G) := by
    rw [hZt]
    exact closure_pair_eq_of_mem ht2 hzK2 hcomm (by rw [← hZt]; exact hconjZ) hx1 hxt
  have centerS_z : centerOf N.S = Subgroup.closure ({t, N.z} : Set G) := by
    rw [hZt]
    exact closure_pair_eq_of_mem ht2 hzK2 hcomm (by rw [← hZt]; exact hzSS) hz1 hzt
  have centerS_E4 : IsFourSubgroup (centerOf N.S) := by
    refine ⟨⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun w hw => ?_⟩, ?_⟩
    · exact Subgroup.mem_centralizer_iff.mp b.2.2 a a.2.1
    · rw [hZt] at hw
      rw [sq]
      rcases mem_closure_pair_of_involutions ht2 hzK2 hcomm hw with h1 | h1 | h1 | h1
      · rw [h1, one_mul]
      · rw [h1]; exact ht2
      · rw [h1]; exact hzK2
      · rw [h1]
        calc t * zK * (t * zK) = t * (zK * t) * zK := by group
          _ = t * (t * zK) * zK := by rw [← hcomm]
          _ = (t * t) * (zK * zK) := by group
          _ = 1 := by rw [ht2, hzK2, one_mul]
    · rw [hZt]
      exact card_closure_pair ht2 hzK2 hcomm ht1 hzK1 hzKt.symm
  have centerT : centerOf T = Subgroup.zpowers N.z := by
    apply le_antisymm
    · intro w hw
      have hwS : w ∈ N.S := N.tuple.center_le hw
      have hwZ : w ∈ centerOf N.S :=
        ⟨hwS, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hS) hw.2⟩
      rw [centerS_z] at hwZ
      have hwx : N.x * w = w * N.x := Subgroup.mem_centralizer_iff.mp hw.2 N.x hxT
      have hzx : N.x * N.z = N.z * N.x := Subgroup.mem_centralizer_iff.mp hzT.2 N.x hxT
      rcases mem_closure_pair_of_involutions ht2 hz2 hcommz hwZ with h1 | h1 | h1 | h1
      · rw [h1]; exact Subgroup.one_mem _
      · exfalso
        apply hxt
        rw [h1] at hwx
        calc N.x⁻¹ * t * N.x = N.x⁻¹ * (t * N.x) := by group
          _ = N.x⁻¹ * (N.x * t) := by rw [← hwx]
          _ = t := by group
      · rw [h1]; exact Subgroup.mem_zpowers _
      · exfalso
        apply hxt
        rw [h1] at hwx
        have h3 : N.x * t * N.z = t * N.x * N.z := by
          calc N.x * t * N.z = N.x * (t * N.z) := by group
            _ = (t * N.z) * N.x := hwx
            _ = t * (N.z * N.x) := by group
            _ = t * (N.x * N.z) := by rw [hzx]
            _ = t * N.x * N.z := by group
        have h4 : N.x * t = t * N.x := mul_right_cancel h3
        calc N.x⁻¹ * t * N.x = N.x⁻¹ * (t * N.x) := by group
          _ = N.x⁻¹ * (N.x * t) := by rw [h4]
          _ = t := by group
    · exact Subgroup.zpowers_le.mpr hzT
  have hzorder : orderOf N.z = 2 := orderOf_eq_prime N.tuple.z_sq hz1
  have hHle : N.H ≤ Subgroup.centralizer ({t} : Set G) := by
    rw [N.H_eq_K0_sup_S]
    exact sup_le (fun k hk => Subgroup.mem_centralizer_singleton_iff.mpr (htK0 k hk))
      (fun s hs' => Subgroup.mem_centralizer_singleton_iff.mpr (htcS s hs'))
  have hE1 : Subgroup.zpowers t ≠ ⊥ := fun h1 => ht1 (Subgroup.zpowers_eq_bot.mp h1)
  have hEle : Subgroup.zpowers t ≤ N.SC := Subgroup.zpowers_le.mpr htSC
  have hEnorm : N.S ≤ Subgroup.normalizer (Subgroup.zpowers t : Set G) := by
    rw [normalizer_zpowers_eq_centralizer ht2]
    intro s hs'
    exact Subgroup.mem_centralizer_singleton_iff.mpr (htcS s hs')
  obtain ⟨hΓ, hSyl, -⟩ := h.concl256 _ hE1 hEle hEnorm
  rw [normalizer_zpowers_eq_centralizer ht2] at hΓ hSyl
  have hnc : ∀ g : G, g⁻¹ * N.z * g ≠ t := by
    intro g hg
    have hle : CFSG.conjugate T g ≤ Subgroup.centralizer ({t} : Set G) := by
      intro w hw
      have hy : g * w * g⁻¹ ∈ T := mem_conjugate_iff.mp hw
      have hyz : (g * w * g⁻¹) * N.z = N.z * (g * w * g⁻¹) :=
        Subgroup.mem_centralizer_iff.mp hzT.2 _ hy
      rw [Subgroup.mem_centralizer_singleton_iff, ← hg]
      calc w * (g⁻¹ * N.z * g) = g⁻¹ * ((g * w * g⁻¹) * N.z) * g := by group
        _ = g⁻¹ * (N.z * (g * w * g⁻¹)) * g := by rw [hyz]
        _ = g⁻¹ * N.z * g * w := by group
    have h2 : IsPGroup 2 ↥(CFSG.conjugate T g) :=
      hs.setting.isPGroup.map (MulAut.conj g⁻¹).toMonoidHom
    have hcard := card_le_twoPart hle h2
    rw [← hSyl.card_eq, card_conjugate] at hcard
    exact N.tuple.lt.ne (Subgroup.eq_of_le_of_card_ge hS hcard)
  exact ⟨t, zK, { zK_mem := hzK0
                  zK_proj := hzKproj
                  t_mem := htSC
                  t_ne_one := ht1
                  t_sq := by rw [sq]; exact ht2
                  centerT := centerT
                  z_order := hzorder
                  centerS_z := centerS_z
                  centerS_x := centerS_x
                  centerS_zK := hZt
                  centerS_E4 := centerS_E4
                  H_le := hHle
                  gammaU := hΓ
                  sylow := hSyl
                  not_conj := hnc }⟩

end CFSG.QuasithinUnique
