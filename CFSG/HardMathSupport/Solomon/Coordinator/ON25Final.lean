module

public import CFSG.HardMathSupport.Solomon.Coordinator.ON25Aux
public import CFSG.HardMathSupport.Solomon.Coordinator.ON25E27
public import CFSG.HardMathSupport.Solomon.Coordinator.ON25Main
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

attribute [local irreducible] dotProduct

open CFSG.RankThree.Native.ONTriple Subgroup CFSG.Open
open scoped commutatorElement

theorem on25_card_comap {G₁ G₂ : Type*} [Group G₁] [Finite G₁] [Group G₂] (q : G₁ →* G₂)
    (hq : Function.Surjective q) (B : Subgroup G₂) :
    Nat.card (B.comap q) = Nat.card B * Nat.card q.ker := by
  let ψ : ↥(B.comap q) →* ↥B := (q.domRestrict (B.comap q)).codRestrict B (fun w => w.2)
  have hψ : Function.Surjective ψ := by
    rintro ⟨b, hb⟩
    obtain ⟨m, rfl⟩ := hq b
    exact ⟨⟨m, hb⟩, Subtype.ext rfl⟩
  have h := Subgroup.card_ker_mul_card_of_surjective (f := ψ) hψ
  have hk : ψ.ker = q.ker.subgroupOf (B.comap q) := by
    ext w
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    constructor
    · intro hw
      exact congrArg Subtype.val hw
    · intro hw
      exact Subtype.ext hw
  have hle : q.ker ≤ B.comap q := fun g hg => by
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hg]
    exact B.one_mem
  rw [hk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h
  rw [← h, mul_comm]

section


theorem on25_E27_contains_z {A : Subgroup GM} (hA : CFSG.RankThree.PartTwo.Late.IsE27 A) :
    zG ∈ A := by
  obtain ⟨h, j, hj, hAh⟩ := exists_conj_AG hA
  have hz : zG ∈ A.map (MulAut.conj h).toMonoidHom := hAh ▸ zG_mem_AG j
  obtain ⟨a, ha, haz⟩ := hz
  have : a = zG := by
    have e1 : (MulAut.conj h⁻¹).toMonoidHom ((MulAut.conj h).toMonoidHom a) = a := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rw [← e1, haz]
    exact conj_zG h⁻¹
  rwa [this] at ha

theorem on25_gen_cover_of_E27 {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y)
    (e : Y ≃* GM) (B : Subgroup Y)
    (hcomm : ∀ x ∈ B, ∀ b ∈ B, x * b * x⁻¹ * b⁻¹ ∈ Subgroup.center Y)
    {A : Subgroup GM} (hA : CFSG.RankThree.PartTwo.Late.IsE27 A)
    (hAU : A ≤ B.map e.toMonoidHom) :
    (⊤ : Subgroup Y) ≤ ⨆ (b : Y) (_ : b ∈ B) (_ : b ∉ Subgroup.center Y),
      GLAPLayer 3 (Subgroup.centralizer ({b} : Set Y)) := by
  have hcenE : (Subgroup.center Y).map e.toMonoidHom = center GM := Subgroup.map_center_eq e
  have hker : e.symm.toMonoidHom.ker ≤ zpowers zG := by
    intro g hg
    have : g = 1 := e.symm.injective (by simpa using hg)
    rw [this]
    exact Subgroup.one_mem _
  refine on25_core hY e.symm.toMonoidHom e.symm.surjective hker ?_
    (on25_hKbar e.symm.toMonoidHom hker e.symm.surjective) B hcomm hA ?_
  · intro a haz hc
    apply haz
    have : e (e.symm a) ∈ (Subgroup.center Y).map e.toMonoidHom := ⟨_, hc, rfl⟩
    rw [hcenE, center_GM] at this
    simpa using this
  · rintro _ ⟨a, ha, rfl⟩
    obtain ⟨b, hb, hab⟩ := hAU ha
    have : e.symm a = b := by rw [← hab]; simp
    show e.symm a ∈ B
    rw [this]
    exact hb



theorem on25_gen_cover {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y)
    (e : Y ≃* GM) (B : Subgroup Y)
    (hBel : IsElemAbelian 3 (B.map (QuotientGroup.mk' (Subgroup.center Y))))
    (hB27 : Nat.card (B.map (QuotientGroup.mk' (Subgroup.center Y))) = 27) :
    (⊤ : Subgroup Y) ≤ ⨆ (b : Y) (_ : b ∈ B) (_ : b ∉ Subgroup.center Y),
      GLAPLayer 3 (Subgroup.centralizer ({b} : Set Y)) := by
  have hcenE : (Subgroup.center Y).map e.toMonoidHom = center GM := Subgroup.map_center_eq e
  have hZ3 : Nat.card (Subgroup.center Y) = 3 := by
    rw [← on25_card_center_GM, ← hcenE, Subgroup.card_map_of_injective e.injective]
  have hcomm := on25_comm_central hBel.1
  have hcard := on25_card_subgroup B
  rw [hB27] at hcard
  have hI : B ⊓ Subgroup.center Y = Subgroup.center Y := by
    by_contra hne
    have hI1 : Nat.card (B ⊓ Subgroup.center Y : Subgroup Y) = 1 := by
      have hd : Nat.card (B ⊓ Subgroup.center Y : Subgroup Y) ∣ 3 :=
        hZ3 ▸ Subgroup.card_dvd_of_le inf_le_right
      rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
      · exact h
      · exact absurd (Subgroup.eq_of_le_of_card_ge
          (inf_le_right : B ⊓ Subgroup.center Y ≤ Subgroup.center Y) (by rw [h, hZ3])) hne
    have hbot : B ⊓ Subgroup.center Y = ⊥ := Subgroup.eq_bot_of_card_eq _ hI1
    have hB27' : Nat.card B = 27 := by rw [hcard, hI1]
    have hE : CFSG.RankThree.PartTwo.Late.IsE27 (B.map e.toMonoidHom) := by
      refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_⟩
      · obtain ⟨_, x, hx, rfl⟩ := a
        obtain ⟨_, y, hy, rfl⟩ := b
        apply Subtype.ext
        show e x * e y = e y * e x
        have hc : x * y * x⁻¹ * y⁻¹ ∈ B ⊓ Subgroup.center Y :=
          ⟨B.mul_mem (B.mul_mem (B.mul_mem hx hy) (B.inv_mem hx)) (B.inv_mem hy),
            hcomm x hx y hy⟩
        rw [hbot, Subgroup.mem_bot] at hc
        have : x * y = y * x := by
          calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
            _ = y * x := by rw [hc, one_mul]
        rw [← map_mul, ← map_mul, this]
      · rintro _ ⟨x, hx, rfl⟩
        have h3 : x ^ 3 ∈ B ⊓ Subgroup.center Y := by
          refine ⟨B.pow_mem hx 3, ?_⟩
          have h4 := hBel.2 _ ⟨x, hx, rfl⟩
          rw [← map_pow] at h4
          exact (QuotientGroup.eq_one_iff _).1 h4
        rw [hbot, Subgroup.mem_bot] at h3
        show (e x) ^ 3 = 1
        rw [← map_pow, h3, map_one]
      · rw [Subgroup.card_map_of_injective e.injective, hB27']
    obtain ⟨b, hb, hbz⟩ := on25_E27_contains_z hE
    have hbc : b ∈ Subgroup.center Y := by
      have : e b ∈ (Subgroup.center Y).map e.toMonoidHom := by
        rw [hcenE]
        show (e b) ∈ center GM
        rw [show e b = zG from hbz, center_GM]
        exact mem_zpowers zG
      obtain ⟨c, hc, hcb⟩ := this
      have : c = b := e.injective hcb
      exact this ▸ hc
    have hb1 : b ∈ B ⊓ Subgroup.center Y := ⟨hb, hbc⟩
    rw [hbot, Subgroup.mem_bot] at hb1
    apply relG.x1
    rw [← show e b = zG from hbz, hb1, map_one]
  have hB81 : Nat.card B = 81 := by rw [hcard, hI, hZ3]
  have hU : Nat.card (B.map e.toMonoidHom) = 81 := by
    rw [Subgroup.card_map_of_injective e.injective, hB81]
  obtain ⟨A, hAU, hA⟩ := on25_exists_E27 hU
  exact on25_gen_cover_of_E27 hY e B (fun x hx b hb => hcomm x hx b hb) hA hAU

theorem on25_gen_simple {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y)
    (hcen : Subgroup.center Y = ⊥) (f : Y ≃* PON.Group) (B : Subgroup Y)
    (hBel : IsElemAbelian 3 (B.map (QuotientGroup.mk' (Subgroup.center Y))))
    (hB27 : Nat.card (B.map (QuotientGroup.mk' (Subgroup.center Y))) = 27) :
    (⊤ : Subgroup Y) ≤ ⨆ (b : Y) (_ : b ∈ B) (_ : b ∉ Subgroup.center Y),
      GLAPLayer 3 (Subgroup.centralizer ({b} : Set Y)) := by
  let q : GM →* Y := f.symm.toMonoidHom.comp (piON.comp modelEquiv.symm.toMonoidHom)
  have hq : Function.Surjective q :=
    f.symm.surjective.comp (piON_surjective.comp modelEquiv.symm.surjective)
  have hkerq : q.ker = zpowers zG := by
    ext g
    rw [MonoidHom.mem_ker]
    show f.symm (piON (modelEquiv.symm g)) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, ker_piON, mem_zpowers_iff, mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [← modelEquiv_zF, ← map_zpow, hk, MulEquiv.apply_symm_apply]
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [← hk, ← modelEquiv_zF, ← map_zpow, MulEquiv.symm_apply_apply]
  have hcomm := on25_comm_central hBel.1
  have hcard := on25_card_subgroup B
  have hB27' : Nat.card B = 27 := by
    rw [hcard, hB27, hcen, inf_bot_eq, Subgroup.card_bot, mul_one]
  have hU : Nat.card (B.comap q) = 81 := by
    rw [on25_card_comap q hq B, hB27', hkerq, on25_card_zG]
  obtain ⟨A, hAU, hA⟩ := on25_exists_E27 hU
  refine on25_core hY q hq hkerq.le ?_ (on25_hKbar q hkerq.le hq) B
    (fun x hx b hb => hcomm x hx b hb) hA (Subgroup.map_le_iff_le_comap.2 hAU)
  intro a haz hc
  rw [hcen, Subgroup.mem_bot] at hc
  apply haz
  rw [← hkerq]
  exact hc

end

end CFSG.HardMathSupport.Solomon.Coordinator
