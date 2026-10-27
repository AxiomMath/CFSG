module

public import CFSG.CGT.T75F.E710Num5
public import CFSG.CGT.T75F.E710Sub
public import CFSG.CGT.T75F.E710Loc5
public import CFSG.CGT.T75F.E710Loc2
public import CFSG.CGT.Timmesfeld75.Sec77
public import CFSG.CGT.Timmesfeld75.Sec78Stmt

public section

namespace CFSG.CGT.T75F

open CFSG.CGT.Timmesfeld75 CFSG.Open

theorem sec710_of (hG : Goldschmidt1974)
    (hA : CFSG.Timmesfeld.Bridge.Asc72.TheoremOne) (h66 : Sec66) (h1 : Sec4NoA) (h62 : Sec62)
    (h63 : Sec63) : Sec710 := by
  intro G _ T T₁ m hc hnat hm2 d hd e he k hk hk3 hord
  have := hc.finite
  have hwcT := hc.hy.pair.wc
  have hcfg := hc.sec3.cfg
  obtain ⟨g, t, htT, ht1, hdg⟩ := hd
  have hy : g * e * g⁻¹ ∈ classD T := classD_conj_mul he g
  have hx : g * d * g⁻¹ = t := by rw [hdg]; group
  have hord' : orderOf (t * (g * e * g⁻¹)) = 2 * k := by
    have e1 : t * (g * e * g⁻¹) = g * (d * e) * g⁻¹ := by rw [← hx]; group
    rw [e1]
    have := MulEquiv.orderOf_eq (MulAut.conj g) (d * e)
    simpa [MulAut.conj_apply, hord] using this
  have hbad := hc.badConfig_of_pair h1 h62 h63 (by omega) hnat htT ht1 hy hk hk3 hord'
  obtain ⟨hN, ε, φ, hcompat, htr⟩ := hc.sec67_transv h1 h63 (by omega) hnat
  have := hN
  let M : TModel T T₁ 3 m := ⟨ε, φ, hcompat, htr⟩
  have h77 : Sec77 := sec77_of h66 h1 h62 h63
  obtain ⟨x, y, z, hl, hyD, hyc, hxy⟩ := exists_loc710 h1 h62 h63 hc hnat hbad
  have hMab : IsElemAbelian 2 (cfgM T T₁) := hcfg.isElemAbelian_cfgM
  have hxL : x ∈ normIn T T₁ := (mem_normIn_iff_comm h63 hc hl.zL hl.z1 hl.xT).2 hl.xz.symm
  have hxM : x ∈ cfgM T T₁ := Cfg.normIn_le_cfgM_left T T₁ hxL
  have hzM : z ∈ cfgM T T₁ := Cfg.normIn_le_cfgM_right T T₁ hl.zL
  have hvM : x * z ∈ cfgM T T₁ := (cfgM T T₁).mul_mem hxM hzM
  have hyM : y ∉ cfgM T T₁ := by
    intro hyM
    have hxyc : x * y = y * x := elemAbelian_mul_comm hMab hxM hyM
    have hy2 : y * y = 1 := mul_self_eq_one_of_mem_classD hwcT.1 hyD
    have hx2 : x * x = 1 := elemAbelian_mul_self hwcT.1 hl.xT
    have h2 : (x * y) ^ 2 = 1 := by
      calc (x * y) ^ 2 = x * y * (x * y) := by rw [pow_two]
        _ = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [hxyc]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [hx2, hy2, one_mul]
    have h3 : orderOf (x * y) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    rw [hxy] at h3
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  classical
  set S : Set G := {e' : G | e' ∈ classD T ∧ e' * (x * z) = (x * z) * e' ∧ e' ∉ cfgM T T₁}
    with hS
  have hyS : y ∈ S := ⟨hyD, hyc, hyM⟩
  let f : G → ℕ := fun e' => Nat.card (Subgroup.closure ((cfgM T T₁ : Set G) ∪ {e'}))
  have hex : ∃ n, ∃ e' ∈ S, f e' = n := ⟨f y, y, hyS, rfl⟩
  obtain ⟨e₀, he₀S, he₀n⟩ := Nat.find_spec hex
  have hmin : ∀ e' ∈ S, f e₀ ≤ f e' := by
    intro e' he'
    rw [he₀n]
    exact Nat.find_min' hex ⟨e', he', rfl⟩
  set X' : Subgroup G := Subgroup.closure ((cfgM T T₁ : Set G) ∪ {e₀}) with hX'
  have hMX : cfgM T T₁ ≤ X' := fun a ha => Subgroup.subset_closure (Or.inl ha)
  have he₀X : e₀ ∈ X' := Subgroup.subset_closure (Or.inr rfl)
  have hXc : X' ≤ Subgroup.centralizer ({x * z} : Set G) := by
    rw [hX', Subgroup.closure_le]
    rintro a (ha | ha)
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact elemAbelian_mul_comm hMab ha hvM
    · rw [Set.mem_singleton_iff] at ha
      subst ha
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact he₀S.2.1
  have hdata : EndgameData X' (classD T) (cfgM T T₁) (normIn T T₁) (2 ^ m) := by
    refine
    { conj_mem := fun d' hd' g _ => classD_conj_mul hd' g
      sq_eq_one := fun d' hd' => mul_self_eq_one_of_mem_classD hwcT.1 hd'
      ne_one := fun d' hd' => ne_one_of_mem_classD hd'
      order := fun d' hd' _ e' he' _ =>
        (hc.sec73 h1 h62 h63 h66 (by omega) hnat hd' he').1
      four := fun d' hd' _ e' he' _ =>
        (hc.sec73 h1 h62 h63 h66 (by omega) hnat hd' he').2
      M_le := hMX
      M_comm := fun a ha b hb => elemAbelian_mul_comm hMab ha hb
      M_sq := fun a ha => elemAbelian_mul_self hMab ha
      M_gen := closure_classD_cfgM hc
      M_card := card_cfgM_three hc
      gen := ?_
      exists_out := ⟨e₀, he₀S.1, he₀X, he₀S.2.2⟩
      H3 := ?_
      q_pow := ⟨m, hm2, rfl⟩
      card_Delta := ?_
      L_le := Cfg.normIn_le_cfgM_left T T₁
      L_card := card_normIn_three hc
      L_D := fun l hl hl1 => mem_classD_of_mem (normIn_le _ _ hl) hl1
      L_TI := ?_
      count65 := fun e' he' heM heL => card_mul_le M h62 h63 hc he' heM heL }
    ·
      intro e' he' he'X he'M
      have hS' : e' ∈ S := ⟨he', (Subgroup.mem_centralizer_singleton_iff.1 (hXc he'X)), he'M⟩
      have hle : Subgroup.closure ((cfgM T T₁ : Set G) ∪ {e'}) ≤ X' := by
        rw [Subgroup.closure_le]
        rintro a (ha | ha)
        · exact hMX ha
        · rw [Set.mem_singleton_iff] at ha
          subst ha
          exact he'X
      have h1' := hmin e' hS'
      have h2' : Nat.card ↥X' ≤ Nat.card ↥(Subgroup.closure ((cfgM T T₁ : Set G) ∪ {e'})) := h1'
      exact Subgroup.eq_of_le_of_card_ge hle h2'
    ·
      intro β hβ hβM d' hd' hd'X hdβ
      exact H3_local M h62 h63 h77 hc hnat hl hβ hβM hd'
        (Subgroup.mem_centralizer_singleton_iff.1 (hXc hd'X)) hdβ
    ·
      rw [Nat.card_coe_set_eq]
      exact ncard_delta_three M h62 h63 hc
    ·
      intro g' hg'X l hl' hl1 hgl l' hl''
      have hlT : l ∈ T := normIn_le _ _ hl'
      have hl₁T : g' * l * g'⁻¹ ∈ T := normIn_le _ _ hgl
      have hl₁1 : g' * l * g'⁻¹ ≠ 1 := by
        intro h
        apply hl1
        have : g' * l * g'⁻¹ = g' * 1 * g'⁻¹ := by rw [h]; group
        simpa using this
      have hinf : T ⊓ conjSubgroup g' T ≠ ⊥ := by
        intro h0
        have : g' * l * g'⁻¹ ∈ T ⊓ conjSubgroup g' T :=
          ⟨hl₁T, mem_conjSubgroup.2 (by
          have e : g'⁻¹ * (g' * l * g'⁻¹) * g' = l := by group
          rw [e]
          exact hlT)⟩
        rw [h0, Subgroup.mem_bot] at this
        exact hl₁1 this
      have hconj : conjSubgroup g' T = T := hwcT.conj_eq_of_inf_ne_bot hinf
      have hl'T : l' ∈ T := normIn_le _ _ hl''
      have h2 : g' * l' * g'⁻¹ ∈ T := by
        have : g' * l' * g'⁻¹ ∈ conjSubgroup g' T := ⟨l', hl'T, by simp [MulAut.conj_apply]⟩
        rwa [hconj] at this
      have h3 : g' * l' * g'⁻¹ ∈ X' :=
        X'.mul_mem (X'.mul_mem hg'X (hMX (Cfg.normIn_le_cfgM_left T T₁ hl''))) (X'.inv_mem hg'X)
      have hcz := Subgroup.mem_centralizer_singleton_iff.1 (hXc h3)
      have hcommx : (g' * l' * g'⁻¹) * x = x * (g' * l' * g'⁻¹) :=
        elemAbelian_mul_comm hwcT.1 h2 hl.xT
      have hcommz : (g' * l' * g'⁻¹) * z = z * (g' * l' * g'⁻¹) := by
        have h4 : x * ((g' * l' * g'⁻¹) * z) = x * (z * (g' * l' * g'⁻¹)) := by
          calc x * ((g' * l' * g'⁻¹) * z) = (x * (g' * l' * g'⁻¹)) * z := by group
            _ = ((g' * l' * g'⁻¹) * x) * z := by rw [hcommx]
            _ = (g' * l' * g'⁻¹) * (x * z) := by group
            _ = (x * z) * (g' * l' * g'⁻¹) := hcz
            _ = x * (z * (g' * l' * g'⁻¹)) := by group
        exact mul_left_cancel h4
      exact (mem_normIn_iff_comm h63 hc hl.zL hl.z1 h2).2 hcommz.symm
  exact endgame710_false hG hA hdata.toEndgame710

end CFSG.CGT.T75F
