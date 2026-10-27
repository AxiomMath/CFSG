module

public import CFSG.LargeExtraspecial.AS35QThY

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35QTh

open Subgroup CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.Blueprint.Fischer (K)

variable {G : Type} [Group G] [Finite G] {S : Setting G}

namespace ThLift

variable (T : ThLift S)

theorem exists_lift_Pbar {pb : S.O} (hpb : pb ∈ S.PbarAsc T.g) :
    ∃ s : G, ∃ hs : s ∈ S.M, s ∈ S.Qa T.g ∧ s * T.Zh = T.Zh * s ∧ S.ρ ⟨s, hs⟩ = pb := by
  classical
  have hpbM : pb ∈ S.Mbar := Subgroup.map_le_range _ _ hpb
  obtain ⟨p₀, hp₀', hp₀e⟩ := hpb
  have hp₀ : (p₀ : G) ∈ S.Qa T.g ⊓ S.M := Subgroup.mem_subgroupOf.mp hp₀'
  have hpbc : T.ζ * pb * T.ζ⁻¹ = pb := by
    rw [← T.hζM pb hpbM, mul_inv_cancel_right]
  have hZM := T.hZhM
  have hZt := T.hZt
  let F := {s : S.M // (s : G) ∈ S.Qa T.g ∧ S.ρ s = pb}
  let σf : F → F := fun s => ⟨⟨T.Zh * s * T.Zh⁻¹,
      S.M.mul_mem (S.M.mul_mem hZM s.1.2) (S.M.inv_mem hZM)⟩,
    S.conj_mem_Qa_of_commute_asc hZt s.2.1, by
      have e : (⟨T.Zh * s * T.Zh⁻¹, S.M.mul_mem (S.M.mul_mem hZM s.1.2) (S.M.inv_mem hZM)⟩ :
          S.M) = ⟨T.Zh, hZM⟩ * s.1 * (⟨T.Zh, hZM⟩ : S.M)⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv, T.hZh, s.2.2, hpbc]⟩
  have hσ3 : ∀ s, σf (σf (σf s)) = s := by
    intro s
    apply Subtype.ext
    apply Subtype.ext
    change T.Zh * (T.Zh * (T.Zh * s.1 * T.Zh⁻¹) * T.Zh⁻¹) * T.Zh⁻¹ = s.1
    rw [show T.Zh * (T.Zh * (T.Zh * (s.1 : G) * T.Zh⁻¹) * T.Zh⁻¹) * T.Zh⁻¹ =
      (T.Zh * T.Zh * T.Zh) * s.1 * (T.Zh * T.Zh * T.Zh)⁻¹ by group, ← pow_three', T.hZ3,
      one_mul, inv_one, mul_one]
  let σ : Equiv.Perm F := ⟨σf, fun s => σf (σf s), fun s => hσ3 s, fun s => hσ3 s⟩
  have hσ : σ ^ 3 ^ 1 = 1 := by
    refine Equiv.ext fun s => ?_
    rw [pow_one, pow_succ, pow_two, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      Equiv.Perm.one_apply]
    exact hσ3 s
  have hp₀Q : ∀ s : F, (p₀ : G)⁻¹ * s.1 ∈ S.Qa T.g ⊓ S.QG := by
    intro s
    refine mem_inf.mpr ⟨(S.Qa T.g).mul_mem ((S.Qa T.g).inv_mem hp₀.1) s.2.1, ?_⟩
    have e : (⟨(p₀ : G)⁻¹ * s.1, S.M.mul_mem (S.M.inv_mem p₀.2) s.1.2⟩ : S.M) = p₀⁻¹ * s.1 := rfl
    refine (S.ρ_eq_one_iff ⟨_, S.M.mul_mem (S.M.inv_mem p₀.2) s.1.2⟩).mp ?_
    rw [e, map_mul, map_inv, hp₀e, s.2.2, inv_mul_cancel]
  have hbij : Function.Bijective (fun s : F => (⟨_, hp₀Q s⟩ : ↥(S.Qa T.g ⊓ S.QG))) := by
    refine ⟨fun s s' h => ?_, fun w => ?_⟩
    · have h1 := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext (mul_left_cancel h1))
    · obtain ⟨hwQa, hwQ⟩ := mem_inf.mp w.2
      have hwM := S.QG_le_M hwQ
      refine ⟨⟨⟨(p₀ : G) * w, S.M.mul_mem p₀.2 hwM⟩, (S.Qa T.g).mul_mem hp₀.1 hwQa, ?_⟩, ?_⟩
      · have e : (⟨(p₀ : G) * w, S.M.mul_mem p₀.2 hwM⟩ : S.M) = p₀ * ⟨w, hwM⟩ := rfl
        rw [e, map_mul, hp₀e, (S.ρ_eq_one_iff _).mpr hwQ, mul_one]
      · apply Subtype.ext
        change (p₀ : G)⁻¹ * (p₀ * w) = w
        group
  have : Fintype F := Fintype.ofFinite F
  have hcard : ¬ 3 ∣ Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, Nat.card_eq_of_bijective _ hbij]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (S.isPGroup_QG.to_le (inf_le_right :
      S.Qa T.g ⊓ S.QG ≤ S.QG))
    rw [hn]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨s, hs⟩ := Equiv.Perm.exists_fixed_point_of_prime hcard hσ
  refine ⟨s.1, s.1.2, s.2.1, ?_, s.2.2⟩
  have h1 : T.Zh * s.1 * T.Zh⁻¹ = s.1 := congrArg (fun x : F => ((x.1 : S.M) : G)) hs
  calc (s.1 : G) * T.Zh = T.Zh * s.1 * T.Zh⁻¹ * T.Zh := by rw [h1]
    _ = T.Zh * s.1 := by group

noncomputable abbrev CZ : Subgroup G := centralizer {T.Zh} ⊓ S.M

theorem mem_CZ {x : G} : x ∈ T.CZ ↔ x * T.Zh = T.Zh * x ∧ x ∈ S.M := by
  rw [mem_inf, mem_centralizer_singleton_iff]

theorem z_mem_CZ : S.z ∈ T.CZ :=
  T.mem_CZ.mpr ⟨(S.z_comm T.hZhM).symm, S.QG_le_M S.z_mem_QG⟩

@[expose] noncomputable def rhoC : T.CZ →* S.Mbar :=
  (S.ρ.comp (inclusion (inf_le_right : T.CZ ≤ S.M))).codRestrict S.Mbar fun _ => ⟨_, rfl⟩

theorem coe_rhoC (c : T.CZ) : (T.rhoC c : S.O) = S.ρ ⟨c, (T.mem_CZ.mp c.2).2⟩ := rfl

theorem rhoC_surjective : Function.Surjective T.rhoC := by
  rintro ⟨_, ⟨m, rfl⟩⟩
  obtain ⟨m', hm', hc, hρ⟩ := T.exists_commute_rho_eq m.2
  exact ⟨⟨m', T.mem_CZ.mpr ⟨hc, hm'⟩⟩, Subtype.ext hρ⟩

theorem exists_psi (hP : S14.Asc512PbarStmt) (hS : S.SixHyp) :
    ∃ ψ : T.CZ →* Multiplicative (ZMod 2), ψ ⟨S.z, T.z_mem_CZ⟩ = Multiplicative.ofAdd 1 := by
  refine exists_hom_of_index_odd (T := ((S.PbarAsc T.g).subgroupOf S.Mbar).comap T.rhoC)
    (T₀ := (S.Qa T.g).comap T.CZ.subtype) (fun c => Subtype.ext ?_) (Subtype.ext S.z_mul_z)
    ?_ ?_ ?_
  · exact S.z_comm (T.mem_CZ.mp c.2).2
  · rw [Subgroup.index_comap_of_surjective _ T.rhoC_surjective]
    have h1 := Subgroup.card_mul_index ((S.PbarAsc T.g).subgroupOf S.Mbar)
    rw [T.card_Mbar hP hS] at h1
    have h2 : Nat.card ((S.PbarAsc T.g).subgroupOf S.Mbar) = 8 := by
      obtain ⟨-, -, hcard, -⟩ := hP G S hS T.g T.hgD T.hgM
      rw [T.hw] at hcard
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (show S.PbarAsc T.g ≤ S.Mbar from Subgroup.map_le_range _ _)).toEquiv, hcard]
      norm_num
    rw [h2] at h1
    rw [show ((S.PbarAsc T.g).subgroupOf S.Mbar).index = 81 by omega]
    decide
  · exact S.z_not_mem_Qa hS.weak (S.ne_z_of_mem_ESet T.hgD.1)
  · intro x hx
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, coe_rhoC] at hx
    obtain ⟨s, hsM, hsQa, hsZ, hsρ⟩ := T.exists_lift_Pbar hx
    obtain ⟨hxZ, hxM⟩ := T.mem_CZ.mp x.2
    have hxsM : (x : G) * s⁻¹ ∈ S.M := S.M.mul_mem hxM (S.M.inv_mem hsM)
    have hxsQ : (x : G) * s⁻¹ ∈ S.QG := by
      have e : (⟨(x : G) * s⁻¹, hxsM⟩ : S.M) = ⟨x, hxM⟩ * (⟨s, hsM⟩ : S.M)⁻¹ := rfl
      refine (S.ρ_eq_one_iff ⟨_, hxsM⟩).mp ?_
      rw [e, map_mul, map_inv, hsρ, mul_inv_cancel]
    have hxsZ : (x : G) * s⁻¹ * T.Zh = T.Zh * ((x : G) * s⁻¹) := by
      have hsZ' : s⁻¹ * T.Zh = T.Zh * s⁻¹ := by
        calc s⁻¹ * T.Zh = s⁻¹ * (T.Zh * s) * s⁻¹ := by group
          _ = s⁻¹ * (s * T.Zh) * s⁻¹ := by rw [hsZ]
          _ = T.Zh * s⁻¹ := by group
      rw [mul_assoc, hsZ', ← mul_assoc, hxZ, mul_assoc]
    rcases T.eq_one_or_z_of_commute hxsQ hxsZ with h | h
    · left
      change (x : G) ∈ S.Qa T.g
      rwa [mul_inv_eq_one.mp h]
    · right
      change (x : G) * S.z ∈ S.Qa T.g
      have hx' : (x : G) = S.z * s := by rw [← h]; group
      rw [hx', mul_assoc, S.z_comm hsM, ← mul_assoc, S.z_mul_z, one_mul]
      exact hsQa

theorem exists_compl (hP : S14.Asc512PbarStmt) (hS : S.SixHyp) :
    ∃ Kc : Subgroup G, Kc ≤ T.CZ ∧ S.z ∉ Kc ∧ ∀ c ∈ T.CZ, c ∈ Kc ∨ c * S.z ∈ Kc := by
  classical
  obtain ⟨ψ, hψ⟩ := T.exists_psi hP hS
  refine ⟨ψ.ker.map T.CZ.subtype, ?_, ?_, fun c hc => ?_⟩
  · rintro _ ⟨c, -, rfl⟩
    exact c.2
  · rintro ⟨c, hc, hcz⟩
    have e : c = ⟨S.z, T.z_mem_CZ⟩ := Subtype.ext hcz
    have hc' : ψ c = 1 := MonoidHom.mem_ker.mp hc
    rw [e, hψ] at hc'
    exact absurd hc' (by decide)
  · by_cases h : ψ ⟨c, hc⟩ = 1
    · exact Or.inl ⟨⟨c, hc⟩, h, rfl⟩
    · refine Or.inr ⟨⟨c, hc⟩ * ⟨S.z, T.z_mem_CZ⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
      rw [map_mul, hψ]
      generalize ψ ⟨c, hc⟩ = a at h ⊢
      revert a
      decide

end ThLift

end CFSG.LargeExtraspecial.AS35QTh
