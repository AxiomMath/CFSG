module

public import CFSG.LocalAnalysis.AGLEmbedding.EscapeTwoCore
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.AGLEmbedding

open CFSG.Open
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_of_forall_mul_mul_inv_mem {R T : Subgroup G}
    (h : ∀ r ∈ R, ∀ t ∈ T, r * t * r⁻¹ ∈ T) : R ≤ Subgroup.normalizer (T : Set G) := by
  intro r hr
  rw [Subgroup.mem_normalizer_iff]
  intro t
  refine ⟨h r hr t, fun ht => ?_⟩
  simpa [mul_assoc] using h r⁻¹ (R.inv_mem hr) _ ht

theorem exists_mem_map_conj_eq_of_card_eq {p : ℕ} [Fact p.Prime] {L P₁ P₂ : Subgroup G}
    (h₁L : P₁ ≤ L) (h₂L : P₂ ≤ L) (h₁ : IsPGroup p P₁) (h₂ : IsPGroup p P₂)
    (hidx : ¬ p ∣ (P₁.subgroupOf L).index) (hcard : Nat.card P₂ = Nat.card P₁) :
    ∃ l ∈ L, P₁.map (MulAut.conj l).toMonoidHom = P₂ := by
  have hc : ∀ {P : Subgroup G}, P ≤ L → Nat.card (P.subgroupOf L) = Nat.card P :=
    fun h => Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv
  have hidx₂ : ¬ p ∣ (P₂.subgroupOf L).index := by
    have e1 := (P₁.subgroupOf L).index_mul_card
    have e2 := (P₂.subgroupOf L).index_mul_card
    rw [hc h₁L] at e1
    rw [hc h₂L, hcard] at e2
    rwa [Nat.eq_of_mul_eq_mul_right Nat.card_pos (e2.trans e1.symm)]
  let S₁ : Sylow p L := (h₁.of_equiv (Subgroup.subgroupOfEquivOfLe h₁L).symm).toSylow hidx
  let S₂ : Sylow p L := (h₂.of_equiv (Subgroup.subgroupOfEquivOfLe h₂L).symm).toSylow hidx₂
  obtain ⟨l, hl⟩ := MulAction.exists_smul_eq L S₁ S₂
  refine ⟨l, l.2, ?_⟩
  have h : (P₁.subgroupOf L).map (MulAut.conj l).toMonoidHom = P₂.subgroupOf L := by
    have h := congrArg (fun T : Sylow p L => (T : Subgroup L)) hl
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
    exact h
  have hcomm : L.subtype.comp (MulAut.conj l).toMonoidHom =
      (MulAut.conj (l : G)).toMonoidHom.comp L.subtype := MonoidHom.ext fun _ => rfl
  have h' := congrArg (Subgroup.map L.subtype) h
  rw [Subgroup.map_map, hcomm, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le h₁L,
    Subgroup.map_subgroupOf_eq_of_le h₂L] at h'
  exact h'

theorem exists_mem_inv_mul_mem_normalizer_of_not_dvd_index {p : ℕ} [Fact p.Prime]
    {L P : Subgroup G} {m : G} (hPL : P ≤ L) (hP : IsPGroup p P)
    (hidx : ¬ p ∣ (P.subgroupOf L).index) (hm : m ∈ Subgroup.normalizer (L : Set G)) :
    ∃ l ∈ L, l⁻¹ * m ∈ Subgroup.normalizer (P : Set G) := by
  have hle : P.map (MulAut.conj m).toMonoidHom ≤ L := by
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hm x).mp (hPL hx)
  obtain ⟨l, hl, hmap⟩ := exists_mem_map_conj_eq_of_card_eq hPL hle hP (hP.map _) hidx
    (Subgroup.card_map_of_injective (MulAut.conj m).injective)
  refine ⟨l, hl, Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_⟩
  have e1 : (MulAut.conj (l⁻¹ * m)).toMonoidHom =
      (MulAut.conj l⁻¹).toMonoidHom.comp (MulAut.conj m).toMonoidHom :=
    MonoidHom.ext fun x => by simp [MulAut.conj_apply, mul_assoc]
  have e2 : (MulAut.conj l⁻¹).toMonoidHom.comp (MulAut.conj l).toMonoidHom =
      MonoidHom.id G := MonoidHom.ext fun x => by simp [MulAut.conj_apply, mul_assoc]
  change P.map (MulAut.conj (l⁻¹ * m)).toMonoidHom = P
  rw [e1, ← Subgroup.map_map, ← hmap, Subgroup.map_map, e2, Subgroup.map_id]

theorem exists_le_normalizer_of_coprime {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {N R : Subgroup G} (hR : IsPGroup p R) (hRN : R ≤ Subgroup.normalizer (N : Set G))
    (hN : p.Coprime (Nat.card N)) :
    ∃ T : Subgroup G, T ≤ N ∧ IsPGroup q T ∧ ¬ q ∣ (T.subgroupOf N).index ∧
      R ≤ Subgroup.normalizer (T : Set G) := by
  let R' : Subgroup (Subgroup.normalizer (N : Set G)) :=
    R.subgroupOf (Subgroup.normalizer (N : Set G))
  have hR' : IsPGroup p R' := hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRN).symm
  have hnd : ¬ p ∣ Nat.card (Sylow q N) := by
    intro hdvd
    let T₀ : Sylow q N := Classical.choice inferInstance
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mp hN
      (hdvd.trans (T₀.card_dvd_index.trans (T₀ : Subgroup N).index_dvd_card))
  obtain ⟨T₀, hT₀⟩ := hR'.nonempty_fixed_point_of_prime_not_dvd_card (Sylow q N) hnd
  refine ⟨(T₀ : Subgroup N).map N.subtype, Subgroup.map_subtype_le _, T₀.isPGroup'.map _, ?_,
    le_normalizer_of_forall_mul_mul_inv_mem ?_⟩
  · rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective N.subtype_injective]
    exact T₀.not_dvd_index
  · rintro r hr _ ⟨t, htT, rfl⟩
    have hrR : (⟨r, hRN hr⟩ : Subgroup.normalizer (N : Set G)) ∈ R' := hr
    have hfix : (⟨r, hRN hr⟩ : Subgroup.normalizer (N : Set G)) • T₀ = T₀ :=
      hT₀ ⟨⟨r, hRN hr⟩, hrR⟩
    have hmem : (⟨r, hRN hr⟩ : Subgroup.normalizer (N : Set G)) • t ∈
        (((⟨r, hRN hr⟩ : Subgroup.normalizer (N : Set G)) • T₀ : Sylow q N) : Subgroup N) := by
      rw [Sylow.pointwise_smul_def]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ htT
    rw [hfix] at hmem
    exact ⟨_, hmem, rfl⟩

omit [Finite G] in
theorem card_sup_eq_mul_of_coprime {X Q : Subgroup G}
    (hXQ : X ≤ Subgroup.normalizer (Q : Set G)) (hcop : Nat.Coprime (Nat.card X) (Nat.card Q)) :
    Nat.card (X ⊔ Q : Subgroup G) = Nat.card X * Nat.card Q := by
  have hset : ((X ⊔ Q : Subgroup G) : Set G) = (X : Set G) * Q :=
    Subgroup.coe_mul_of_left_le_normalizer_right X Q hXQ
  have h1 : Nat.card (X ⊔ Q : Subgroup G) = Nat.card ((X : Set G) * Q : Set G) := by
    rw [← hset]
    rfl
  rw [h1, Subgroup.card_mul_eq_card_subgroup_mul_card_quotient Q (X : Set G)]
  have hinj : Set.InjOn (fun x : G => (x : G ⧸ Q)) (X : Set G) := by
    intro a ha b hb hab
    have hmem : a⁻¹ * b ∈ X ⊓ Q := ⟨X.mul_mem (X.inv_mem ha) hb, QuotientGroup.eq.mp hab⟩
    rw [disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop), Subgroup.mem_bot] at hmem
    exact inv_mul_eq_one.mp hmem
  rw [Nat.card_image_of_injOn hinj, mul_comm]
  rfl

theorem index_subgroupOf_sup_eq_card {X Q : Subgroup G}
    (hXQ : X ≤ Subgroup.normalizer (Q : Set G)) (hcop : Nat.Coprime (Nat.card X) (Nat.card Q)) :
    (X.subgroupOf (X ⊔ Q)).index = Nat.card Q := by
  have e := (X.subgroupOf (X ⊔ Q)).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : X ≤ X ⊔ Q)).toEquiv,
    card_sup_eq_mul_of_coprime hXQ hcop, mul_comm (Nat.card X)] at e
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos e

theorem le_of_le_of_isPGroup_of_not_dvd_index {q : ℕ} [Fact q.Prime] {T U N : Subgroup G}
    (hTU : T ≤ U) (hUN : U ≤ N) (hU : IsPGroup q U) (hidx : ¬ q ∣ (T.subgroupOf N).index) :
    U ≤ T := by
  have hrel := Subgroup.relIndex_mul_relIndex T U N hTU hUN
  obtain ⟨k, hk⟩ := hU.index (T.subgroupOf U)
  rcases k with _ | k
  · rw [pow_zero] at hk
    exact Subgroup.relIndex_eq_one.mp hk
  · exact absurd (Dvd.intro _ hrel) fun h => hidx
      ((dvd_pow_self q (Nat.succ_ne_zero k)).trans (hk ▸ h))

omit [Finite G] in
theorem le_of_le_sup_of_isPGroup_of_ne {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {X N U : Subgroup G} (hX : IsPGroup p X) (hXN : X ≤ Subgroup.normalizer (N : Set G))
    (hU : IsPGroup q U) (hUXN : U ≤ X ⊔ N) : U ≤ N := by
  let L := X ⊔ N
  have hnorm : (N.subgroupOf L).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hXN
  let π := QuotientGroup.mk' (N.subgroupOf L)
  have htop : (X.subgroupOf L).map π = ⊤ := by
    have hcod : X.subgroupOf L ⊔ N.subgroupOf L = ⊤ :=
      codisjoint_iff.mp (Subgroup.codisjoint_subgroupOf_sup X N)
    have hN : (N.subgroupOf L).map π = ⊥ :=
      (Subgroup.map_eq_bot_iff _).mpr (le_of_eq (QuotientGroup.ker_mk' _).symm)
    rw [← Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective _), ← hcod,
      Subgroup.map_sup, hN, sup_bot_eq]
  have hXp : IsPGroup p (X.subgroupOf L) :=
    hX.of_equiv (Subgroup.subgroupOfEquivOfLe (le_sup_left : X ≤ X ⊔ N)).symm
  have hUq : IsPGroup q (U.subgroupOf L) := hU.of_equiv (Subgroup.subgroupOfEquivOfLe hUXN).symm
  have h1 : IsPGroup p ((U.subgroupOf L).map π) :=
    (hXp.map π).to_le (by rw [htop]; exact le_top)
  have hbot : (U.subgroupOf L).map π = ⊥ :=
    disjoint_self.mp (IsPGroup.disjoint_of_ne p q hpq _ _ h1 (hUq.map π))
  intro u hu
  have hker : (⟨u, hUXN hu⟩ : L) ∈ π.ker := (Subgroup.map_eq_bot_iff _).mp hbot hu
  rw [QuotientGroup.ker_mk'] at hker
  exact hker

theorem not_dvd_index_of_inf_normalizer_le {q : ℕ} [Fact q.Prime] {T N D : Subgroup G}
    (hTN : T ≤ N) (hND : N ≤ D) (hT : IsPGroup q T) (hidx : ¬ q ∣ (T.subgroupOf N).index)
    (hle : ∀ U : Subgroup G, IsPGroup q U → U ≤ D ⊓ Subgroup.normalizer (T : Set G) → U ≤ N) :
    ¬ q ∣ (T.subgroupOf D).index := by
  intro hdvd
  have hTD : T ≤ D := hTN.trans hND
  obtain ⟨P, hP⟩ := (hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTD).symm).exists_le_sylow
  have hne : T.subgroupOf D ≠ P := fun h => P.not_dvd_index (h ▸ hdvd)
  have hTP : T < (P : Subgroup D).map D.subtype := by
    refine lt_of_le_of_ne ?_ fun h => hne ?_
    · rw [← Subgroup.map_subgroupOf_eq_of_le hTD]
      exact Subgroup.map_mono hP
    · rw [h]
      exact Subgroup.comap_map_eq_self_of_injective D.subtype_injective _
  have hP2 : IsPGroup q ((P : Subgroup D).map D.subtype) := P.isPGroup'.map _
  obtain ⟨y, hyP, hyT, hyN⟩ := exists_mem_normalizer_not_mem_of_lt_of_isPGroup hP2 hTP
  have hU := hle (((P : Subgroup D).map D.subtype) ⊓ Subgroup.normalizer (T : Set G))
    (hP2.to_le inf_le_left) (inf_le_inf_right _ (Subgroup.map_subtype_le _))
  exact hyT (le_of_le_of_isPGroup_of_not_dvd_index (le_inf hTP.le Subgroup.le_normalizer) hU
    (hP2.to_le inf_le_left) hidx ⟨hyP, hyN⟩)

omit [Finite G] in
theorem isSubnormal_of_isSubnormal_of_normal {Y D M : Subgroup G} (hY : IsSubnormal Y D)
    (hDM : D ≤ M) (hD : (D.subgroupOf M).Normal) : IsSubnormal Y M :=
  hY.trans (.step hDM hD (.refl M))

section CentralizerProduct

variable {X Q M : Subgroup G}

omit [Finite G] in
theorem exists_mul_of_mem_sup_inf_centralizer (hMQ : M ≤ Subgroup.normalizer (Q : Set G))
    {d : G} (hd : d ∈ Q ⊔ (M ⊓ Subgroup.centralizer (X : Set G))) :
    ∃ q ∈ Q, ∃ c ∈ M ⊓ Subgroup.centralizer (X : Set G), q * c = d := by
  have h : d ∈ ((Q ⊔ (M ⊓ Subgroup.centralizer (X : Set G)) : Subgroup G) : Set G) := hd
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Q _ (inf_le_left.trans hMQ)] at h
  exact h

omit [Finite G] in
theorem commutator_mem_of_mem_sup_inf_centralizer (hXM : X ≤ M)
    (hMQ : M ≤ Subgroup.normalizer (Q : Set G)) {d y : G}
    (hd : d ∈ Q ⊔ (M ⊓ Subgroup.centralizer (X : Set G))) (hy : y ∈ X ⊔ Q) :
    d * y * d⁻¹ * y⁻¹ ∈ Q := by
  obtain ⟨q, hq, c, hc, rfl⟩ := exists_mul_of_mem_sup_inf_centralizer hMQ hd
  have hy' : y ∈ ((X ⊔ Q : Subgroup G) : Set G) := hy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right X Q (hXM.trans hMQ)] at hy'
  obtain ⟨x, hx, q', hq', rfl⟩ := hy'
  have hcx : c * x * c⁻¹ = x := by
    rw [← Subgroup.mem_centralizer_iff.mp hc.2 x hx]
    group
  have hcq : c * q' * c⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hMQ hc.1) q').mp hq'
  have e : q * c * (x * q') * (q * c)⁻¹ * (x * q')⁻¹ =
      q * ((c * x * c⁻¹) * ((c * q' * c⁻¹) * q⁻¹ * q'⁻¹) * x⁻¹) := by group
  rw [e, hcx]
  exact Q.mul_mem hq ((Subgroup.mem_normalizer_iff.mp (hMQ (hXM hx)) _).mp
    (Q.mul_mem (Q.mul_mem hcq (Q.inv_mem hq)) (Q.inv_mem hq')))

variable {p : ℕ} [Fact p.Prime]

theorem mem_sup_inf_centralizer_of_commutator_mem (hX : IsPGroup p X)
    (hQ : p.Coprime (Nat.card Q)) (hXM : X ≤ M) (hQM : Q ≤ M)
    (hMQ : M ≤ Subgroup.normalizer (Q : Set G))
    (hMXQ : M ≤ Subgroup.normalizer ((X ⊔ Q : Subgroup G) : Set G)) {n : G} (hn : n ∈ M)
    (hnX : ∀ x ∈ X, n * x * n⁻¹ * x⁻¹ ∈ Q) :
    n ∈ Q ⊔ (M ⊓ Subgroup.centralizer (X : Set G)) := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hX
  have hcop : Nat.Coprime (Nat.card X) (Nat.card Q) := hk ▸ hQ.pow_left k
  have hXNQ : X ≤ Subgroup.normalizer (Q : Set G) := hXM.trans hMQ
  have hidx : ¬ p ∣ (X.subgroupOf (X ⊔ Q)).index := by
    rw [index_subgroupOf_sup_eq_card hXNQ hcop]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mp hQ
  obtain ⟨l, hl, hln⟩ :=
    exists_mem_inv_mul_mem_normalizer_of_not_dvd_index le_sup_left hX hidx (hMXQ hn)
  have hl' : l ∈ ((Q ⊔ X : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact hl
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Q X hXNQ] at hl'
  obtain ⟨q, hq, x₀, hx₀, rfl⟩ := hl'
  have hcN : q⁻¹ * n ∈ Subgroup.normalizer (X : Set G) := by
    have e : q⁻¹ * n = x₀ * ((q * x₀)⁻¹ * n) := by group
    rw [e]
    exact (Subgroup.normalizer (X : Set G)).mul_mem (Subgroup.le_normalizer hx₀) hln
  have hcC : q⁻¹ * n ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 : q⁻¹ * n * x * (q⁻¹ * n)⁻¹ * x⁻¹ ∈ X :=
      X.mul_mem ((Subgroup.mem_normalizer_iff.mp hcN x).mp hx) (X.inv_mem hx)
    have h2 : q⁻¹ * n * x * (q⁻¹ * n)⁻¹ * x⁻¹ ∈ Q := by
      have e : q⁻¹ * n * x * (q⁻¹ * n)⁻¹ * x⁻¹ =
          q⁻¹ * (n * x * n⁻¹ * x⁻¹) * (x * q * x⁻¹) := by group
      rw [e]
      exact Q.mul_mem (Q.mul_mem (Q.inv_mem hq) (hnX x hx))
        ((Subgroup.mem_normalizer_iff.mp (hMQ (hXM hx)) q).mp hq)
    have h3 : q⁻¹ * n * x * (q⁻¹ * n)⁻¹ * x⁻¹ ∈ X ⊓ Q := ⟨h1, h2⟩
    rw [disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop), Subgroup.mem_bot] at h3
    have e : x * (q⁻¹ * n) = (q⁻¹ * n * x * (q⁻¹ * n)⁻¹ * x⁻¹)⁻¹ * (q⁻¹ * n * x) := by group
    rw [e, h3, inv_one, one_mul]
  have e : n = q * (q⁻¹ * n) := by group
  rw [e]
  exact Subgroup.mul_mem_sup hq ⟨M.mul_mem (M.inv_mem (hQM hq)) hn, hcC⟩

theorem le_normalizer_sup_inf_centralizer (hX : IsPGroup p X) (hQ : p.Coprime (Nat.card Q))
    (hXM : X ≤ M) (hQM : Q ≤ M) (hMQ : M ≤ Subgroup.normalizer (Q : Set G))
    (hMXQ : M ≤ Subgroup.normalizer ((X ⊔ Q : Subgroup G) : Set G)) :
    M ≤ Subgroup.normalizer
      ((Q ⊔ (M ⊓ Subgroup.centralizer (X : Set G)) : Subgroup G) : Set G) := by
  have hDM : Q ⊔ (M ⊓ Subgroup.centralizer (X : Set G)) ≤ M := sup_le hQM inf_le_left
  refine le_normalizer_of_forall_mul_mul_inv_mem fun m hm d hd => ?_
  refine mem_sup_inf_centralizer_of_commutator_mem hX hQ hXM hQM hMQ hMXQ
    (M.mul_mem (M.mul_mem hm (hDM hd)) (M.inv_mem hm)) fun x hx => ?_
  have hy : m⁻¹ * x * m ∈ X ⊔ Q := by
    simpa using
      (Subgroup.mem_normalizer_iff.mp (hMXQ (M.inv_mem hm)) x).mp (Subgroup.mem_sup_left hx)
  have e : m * d * m⁻¹ * x * (m * d * m⁻¹)⁻¹ * x⁻¹ =
      m * (d * (m⁻¹ * x * m) * d⁻¹ * (m⁻¹ * x * m)⁻¹) * m⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (hMQ hm) _).mp
    (commutator_mem_of_mem_sup_inf_centralizer hXM hMQ hd hy)

end CentralizerProduct

end CFSG.AGLEmbedding
