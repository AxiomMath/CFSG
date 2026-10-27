module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62xLift
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

section Comm

variable {G : Type} [Group G]

private theorem final62x_isMulCommutative_of {H : Subgroup G}
    (h : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) : IsMulCommutative H :=
  ⟨⟨fun a b => Subtype.ext (h a a.2 b b.2)⟩⟩

private theorem final62x_comm {H : Subgroup G} (hH : IsMulCommutative H) {a b : G} (ha : a ∈ H)
    (hb : b ∈ H) : a * b = b * a :=
  congrArg Subtype.val (hH.is_comm.comm (⟨a, ha⟩ : H) ⟨b, hb⟩)

private theorem final62x_le_of_isSubnormal {H K : Subgroup G} (h : IsSubnormal H K) : H ≤ K :=
  h.le

private theorem final62x_isKGroup_of_section {A B : Type} [Group A] [Group B]
    (hA : CFSG.IsKGroup A) (H : Subgroup A) (π : H →* B) (hπ : Function.Surjective π) :
    CFSG.IsKGroup B :=
  (hA.subgroup H).of_surjective π hπ


private noncomputable def final62xPsi (J O : Subgroup G) [(O.subgroupOf (J ⊔ O)).Normal] :
    ↥J →* ↥(J ⊔ O) ⧸ O.subgroupOf (J ⊔ O) :=
  (QuotientGroup.mk' (O.subgroupOf (J ⊔ O))).comp (Subgroup.inclusion (le_sup_left : J ≤ J ⊔ O))

private theorem final62xPsi_eq_one_iff (J O : Subgroup G) [(O.subgroupOf (J ⊔ O)).Normal]
    (j : ↥J) : final62xPsi J O j = 1 ↔ (j : G) ∈ O := by
  unfold final62xPsi
  simp [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

private theorem final62xPsi_surjective (J O : Subgroup G) [hn : (O.subgroupOf (J ⊔ O)).Normal] :
    Function.Surjective (final62xPsi J O) := by
  intro z
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective z
  have hsup : J.subgroupOf (J ⊔ O) ⊔ O.subgroupOf (J ⊔ O) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
    exact Subgroup.subgroupOf_self (J ⊔ O)
  have hk : k ∈ J.subgroupOf (J ⊔ O) ⊔ O.subgroupOf (J ⊔ O) := by rw [hsup]; trivial
  have hmul := Subgroup.mul_normal (J.subgroupOf (J ⊔ O)) (O.subgroupOf (J ⊔ O))
  rw [← SetLike.mem_coe, hmul] at hk
  obtain ⟨j', hj', o', ho', rfl⟩ := hk
  refine ⟨⟨(j' : G), hj'⟩, ?_⟩
  have ho1 : (QuotientGroup.mk o' : ↥(J ⊔ O) ⧸ O.subgroupOf (J ⊔ O)) = 1 :=
    (QuotientGroup.eq_one_iff o').2 ho'
  have hj'eq : Subgroup.inclusion (le_sup_left : J ≤ J ⊔ O) ⟨(j' : G), hj'⟩ = j' :=
    Subtype.ext rfl
  change QuotientGroup.mk (Subgroup.inclusion (le_sup_left : J ≤ J ⊔ O) ⟨(j' : G), hj'⟩) =
    QuotientGroup.mk (j' * o')
  rw [hj'eq, QuotientGroup.mk_mul, ho1, mul_one]

private theorem final62xPsi_ker_card_dvd (J O : Subgroup G) [(O.subgroupOf (J ⊔ O)).Normal] :
    Nat.card (final62xPsi J O).ker ∣ Nat.card O := by
  let κ : (final62xPsi J O).ker →* O :=
    ((J.subtype).comp (final62xPsi J O).ker.subtype).codRestrict O fun j =>
      (final62xPsi_eq_one_iff J O j.1).1 (MonoidHom.mem_ker.1 j.2)
  refine Subgroup.card_dvd_of_injective κ fun x y hxy => ?_
  exact Subtype.ext (Subtype.ext (congrArg (fun t : ↥O => (t : G)) hxy))

end Comm

section Aux

variable {G : Type} [Group G] [Finite G]

private theorem final62x_le_pRank {f k : ℕ} (hf : 1 < f) {H E : Subgroup G} (hEH : E ≤ H)
    (hE : IsElemAbelian f E) (hcard : Nat.card E = f ^ k) : k ≤ CFSG.Open.pRank f H :=
  CFSG.SectionRank.le_pRank hf hEH hE hcard

private theorem final62x_card_eq_pow_pRank {f : ℕ} (hf : f.Prime) {E : Subgroup G}
    (hE : IsElemAbelian f E) : Nat.card E = f ^ CFSG.Open.pRank f E := by
  have : Fact f.Prime := ⟨hf⟩
  have hp : IsPGroup f E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 (g : G) g.2)⟩
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have h1 : k ≤ CFSG.Open.pRank f E := final62x_le_pRank hf.one_lt le_rfl hE hk
  have h2 : CFSG.Open.pRank f E ≤ k := by
    unfold CFSG.Open.pRank
    refine csSup_le' ?_
    rintro r ⟨E', hE'E, -, hcard⟩
    have : f ^ r ≤ f ^ k := by
      rw [← hcard, ← hk]
      exact Subgroup.card_le_of_le hE'E
    exact (Nat.pow_le_pow_iff_right hf.one_lt).mp this
  rw [hk, le_antisymm h1 h2]

private theorem final62x_comm_of_isPGroup {f : ℕ} (hf : f.Prime) {E Q : Subgroup G}
    (hE : IsPGroup f E) (hEi : ¬ f ∣ E.index) (hEc : IsMulCommutative E) (hQ : IsPGroup f Q) :
    IsMulCommutative Q := by
  have : Fact f.Prime := ⟨hf⟩
  let S : Sylow f G := hE.toSylow hEi
  obtain ⟨S', hQS'⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S S'
  refine final62x_isMulCommutative_of fun a ha b hb => ?_
  have ha' : a ∈ ((g • S : Sylow f G) : Subgroup G) := hg ▸ hQS' ha
  have hb' : b ∈ ((g • S : Sylow f G) : Subgroup G) := hg ▸ hQS' hb
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at ha' hb'
  obtain ⟨s, hs, rfl⟩ := ha'
  obtain ⟨t, ht, rfl⟩ := hb'
  have h := final62x_comm hEc (by simpa [S] using hs) (by simpa [S] using ht)
  simp only [MulAut.smul_def, MulAut.conj_apply]
  calc g * s * g⁻¹ * (g * t * g⁻¹) = g * (s * t) * g⁻¹ := by group
    _ = g * (t * s) * g⁻¹ := by rw [h]
    _ = g * t * g⁻¹ * (g * s * g⁻¹) := by group

theorem false_of_closing_paragraph (hK : KFactAbelianSylowRankThree) {f : ℕ} (hf : f.Prime)
    (hf2 : f ≠ 2) {F E : Subgroup G} (hFe : IsElemAbelian f F) (hF4 : Nat.card F = f ^ 4)
    (hE : IsPGroup f E) (hEi : ¬ f ∣ E.index) (hEc : IsMulCommutative E)
    (hN : ∀ a ∈ F, a ≠ 1 → ∀ g ∈ normalizer (F : Set G) ⊓ centralizer ({a} : Set G),
      ∃ n : ℕ, g ^ (2 ^ n) ∈ centralizer (F : Set G))
    {a : G} (haF : a ∈ F) (ha1 : a ≠ 1) (hKa : CFSG.IsKGroup ↥(centralizer ({a} : Set G)))
    {J : Subgroup G} (hJ : lBalanceIsPComponent f (centralizer ({a} : Set G)) J)
    (hJ3 : CFSG.Open.pRank f J = 3) (hFJ : CFSG.Open.pRank f (F ⊓ J) = 3) : False := by
  have hfact : Fact f.Prime := ⟨hf⟩
  obtain ⟨hJsub, ⟨-, hKsub, hnormO, hq⟩, -⟩ := hJ
  have hJX : J ≤ centralizer ({a} : Set G) := final62x_le_of_isSubnormal hJsub
  obtain ⟨hOX, -, hOcop⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec f
    (centralizer ({a} : Set G))
  have hOX' : lBalancePrimeCore f (centralizer ({a} : Set G)) ≤ centralizer ({a} : Set G) := hOX
  have hOcop' : Nat.Coprime f (Nat.card (lBalancePrimeCore f (centralizer ({a} : Set G)))) :=
    hOcop
  generalize lBalancePrimeCore f (centralizer ({a} : Set G)) = O at hOX' hOcop' hnormO hq
  have hKX : J ⊔ O ≤ centralizer ({a} : Set G) := sup_le hJX hOX'
  have hcentJ : ∀ j ∈ J, j * a = a * j := fun j hj =>
    Subgroup.mem_centralizer_singleton_iff.1 (hJX hj)
  have hn : (O.subgroupOf (J ⊔ O)).Normal := hnormO
  let Z := ↥(J ⊔ O) ⧸ O.subgroupOf (J ⊔ O)
  let ψ : ↥J →* Z := final62xPsi J O
  have hψ : Function.Surjective ψ := final62xPsi_surjective J O
  have hker : Nat.Coprime f (Nat.card ψ.ker) :=
    Nat.Coprime.coprime_dvd_right (final62xPsi_ker_card_dvd J O) hOcop'
  have hkerO : ∀ j : ↥J, ψ j = 1 → (j : G) ∈ O := fun j hj =>
    (final62xPsi_eq_one_iff J O j).1 hj
  have hZ : CFSG.IsKGroup Z :=
    final62x_isKGroup_of_section hKa ((J ⊔ O).subgroupOf (centralizer ({a} : Set G)))
      ((QuotientGroup.mk' (O.subgroupOf (J ⊔ O))).comp
        (Subgroup.subgroupOfEquivOfLe hKX).toMonoidHom)
      ((QuotientGroup.mk'_surjective _).comp (Subgroup.subgroupOfEquivOfLe hKX).surjective)
  have hF₁e : IsElemAbelian f (F ⊓ J) :=
    ⟨final62x_isMulCommutative_of fun u hu v hv => final62x_comm hFe.1 hu.1 hv.1,
      fun x hx => hFe.2 x hx.1⟩
  have hF₁card : Nat.card (F ⊓ J : Subgroup G) = f ^ 3 := by
    rw [final62x_card_eq_pow_pRank hf hF₁e, hFJ]
  let F₁' : Subgroup ↥J := (F ⊓ J).subgroupOf J
  have hF₁'p : IsPGroup f F₁' := fun y =>
    ⟨1, Subtype.ext (Subtype.ext (by
      simpa using hFe.2 ((y.1 : ↥J) : G) (Subgroup.mem_subgroupOf.1 y.2).1))⟩
  obtain ⟨Q, hQ⟩ := hF₁'p.exists_le_sylow
  have hP : IsPGroup f (Q : Subgroup ↥J) := Q.isPGroup'
  have hPi : ¬ f ∣ (Q : Subgroup ↥J).index := Q.not_dvd_index
  have hPc : IsMulCommutative (Q : Subgroup ↥J) := by
    have hc := final62x_comm_of_isPGroup hf hE hEi hEc (hP.map J.subtype)
    refine final62x_isMulCommutative_of fun u hu v hv => ?_
    exact Subtype.ext (final62x_comm hc (a := (u : G)) (b := (v : G)) ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩)
  have hcomm : ∀ u v : ↥J, u ∈ (Q : Subgroup ↥J) → v ∈ (Q : Subgroup ↥J) → Commute u v :=
    fun u v hu hv => final62x_comm hPc hu hv
  let AY : Subgroup ↥J :=
    { carrier := {y | y ∈ (Q : Subgroup ↥J) ∧ y ^ f = 1}
      one_mem' := ⟨one_mem _, one_pow f⟩
      mul_mem' := fun {u v} hu hv => ⟨mul_mem hu.1 hv.1, by
        rw [(hcomm u v hu.1 hv.1).mul_pow, hu.2, hv.2, one_mul]⟩
      inv_mem' := fun {u} hu => ⟨inv_mem hu.1, by rw [inv_pow, hu.2, inv_one]⟩ }
  have hF₁'le : F₁' ≤ AY := fun y hy =>
    ⟨hQ hy, Subtype.ext (by simpa using hFe.2 (y : G) (Subgroup.mem_subgroupOf.1 hy).1)⟩
  have hAYp : IsPGroup f AY := fun y => ⟨1, Subtype.ext (by simpa using y.2.2)⟩
  have hAYcard : Nat.card AY ≤ f ^ 3 := by
    obtain ⟨k, hk⟩ := hAYp.exists_card_eq
    have hAYe : IsElemAbelian f (AY.map J.subtype) := by
      refine ⟨final62x_isMulCommutative_of ?_, ?_⟩
      · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
        exact congrArg Subtype.val (final62x_comm hPc hu.1 hv.1)
      · rintro _ ⟨u, hu, rfl⟩
        simpa using congrArg Subtype.val hu.2
    have hcard : Nat.card (AY.map J.subtype) = f ^ k := by
      rw [Subgroup.card_map_of_injective J.subtype_injective, hk]
    have hk3 : k ≤ 3 := hJ3 ▸ final62x_le_pRank hf.one_lt (Subgroup.map_subtype_le AY) hAYe hcard
    rw [hk]
    exact Nat.pow_le_pow_right hf.pos hk3
  have hF₁'card : Nat.card F₁' = f ^ 3 := by
    rw [← hF₁card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : F ⊓ J ≤ J)).toEquiv
  have hAYeq : F₁' = AY :=
    Subgroup.eq_of_le_of_card_ge hF₁'le (by rw [hF₁'card]; exact hAYcard)
  have hA1 : ∀ y ∈ F₁', y ^ f = 1 := fun y hy => (hF₁'le hy).2
  have hA2 : ∀ y ∈ (Q : Subgroup ↥J), y ^ f = 1 → y ∈ F₁' := fun y hy hyf => by
    rw [hAYeq]; exact ⟨hy, hyf⟩
  have haJ : a ∉ J := by
    intro haJ
    have hcent : ψ ⟨a, haJ⟩ ∈ center Z := by
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨j, rfl⟩ := hψ w
      rw [← map_mul, ← map_mul]
      exact congrArg ψ (Subtype.ext (hcentJ j j.2))
    have haf : a ^ f = 1 := hFe.2 a haF
    have hzf : ψ ⟨a, haJ⟩ ^ f = 1 := by
      rw [← map_pow]
      have : (⟨a, haJ⟩ : ↥J) ^ f = 1 := Subtype.ext (by simpa using haf)
      rw [this, map_one]
    obtain ⟨hQp, hQi⟩ := lift62x_sylow_map ψ hψ hP hPi
    have hQc : IsMulCommutative ((Q : Subgroup ↥J).map ψ) := by
      refine final62x_isMulCommutative_of ?_
      rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg ψ (final62x_comm hPc hu hv)
    have h1 := lift62x_center_eq_one hq.1 hf hQp hQi hQc hcent hzf
    have haO : a ∈ O := hkerO ⟨a, haJ⟩ h1
    have hord : orderOf a = f := orderOf_eq_prime haf ha1
    have hdvd : f ∣ Nat.card O := hord ▸ Subgroup.orderOf_dvd_natCard O haO
    exact hf.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hOcop' hdvd)
  have haF₁ : a ∉ F ⊓ J := fun h => haJ h.2
  have hFeq : (F ⊓ J) ⊔ zpowers a = F := by
    have hle : (F ⊓ J) ⊔ zpowers a ≤ F := sup_le inf_le_left (Subgroup.zpowers_le.2 haF)
    have hlt : F ⊓ J < (F ⊓ J) ⊔ zpowers a := by
      refine lt_of_le_of_ne le_sup_left fun h => haF₁ ?_
      rw [h]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
    have hdvd : Nat.card ((F ⊓ J) ⊔ zpowers a : Subgroup G) ∣ f ^ 4 :=
      hF4 ▸ Subgroup.card_dvd_of_le hle
    obtain ⟨j, hj, hjcard⟩ := (Nat.dvd_prime_pow hf).1 hdvd
    have h3j : 3 ≤ j := by
      have := Subgroup.card_dvd_of_le (le_sup_left : F ⊓ J ≤ (F ⊓ J) ⊔ zpowers a)
      rw [hF₁card, hjcard] at this
      exact (Nat.pow_dvd_pow_iff_le_right hf.one_lt).1 this
    have hj4 : j = 4 := by
      by_contra hne
      have hj3 : j = 3 := by omega
      exact hlt.ne (Subgroup.eq_of_le_of_card_ge (le_sup_left : F ⊓ J ≤ (F ⊓ J) ⊔ zpowers a)
        (by rw [hF₁card, hjcard, hj3]))
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hF4, hjcard, hj4])
  obtain ⟨y, hyN, hy⟩ :=
    lift62x_core hK hZ hq ψ hψ hf hf2 hker hP hPi hPc hQ hF₁'card hA1 hA2
  have hconjF₁ : ∀ y' : ↥J, y' ∈ normalizer ((Q : Subgroup ↥J) : Set ↥J) →
      ∀ u ∈ F ⊓ J, (y' : G) * u * (y' : G)⁻¹ ∈ F ⊓ J := by
    intro y' hy' u hu
    have hu' : (⟨u, hu.2⟩ : ↥J) ∈ F₁' := Subgroup.mem_subgroupOf.2 hu
    have hmemP : y' * ⟨u, hu.2⟩ * y'⁻¹ ∈ (Q : Subgroup ↥J) :=
      (Subgroup.mem_normalizer_iff.1 hy' _).1 (hQ hu')
    have hpow : (y' * ⟨u, hu.2⟩ * y'⁻¹) ^ f = 1 := by
      rw [conj_pow, hA1 _ hu', mul_one, mul_inv_cancel]
    have hmem := Subgroup.mem_subgroupOf.1 (hA2 _ hmemP hpow)
    simpa using hmem
  have hnormF₁ : ∀ y' : ↥J, y' ∈ normalizer ((Q : Subgroup ↥J) : Set ↥J) →
      (y' : G) ∈ normalizer ((F ⊓ J : Subgroup G) : Set G) := by
    intro y' hy'
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hconjF₁ y' hy' h hh, fun hh => ?_⟩
    have := hconjF₁ y'⁻¹ (inv_mem hy') _ hh
    simpa [mul_assoc] using this
  have hnormF : ∀ y' : ↥J, y' ∈ normalizer ((Q : Subgroup ↥J) : Set ↥J) →
      (y' : G) ∈ normalizer (F : Set G) := by
    intro y' hy'
    have hcomm' : (y' : G) * a * (y' : G)⁻¹ = a := by
      rw [mul_inv_eq_iff_eq_mul]; exact hcentJ _ y'.2
    rw [← hFeq, Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (hnormF₁ y' hy'), MonoidHom.map_zpowers]
    simp [MulAut.conj_apply, hcomm']
  have hyNF : (y : G) ∈ normalizer (F : Set G) ⊓ centralizer ({a} : Set G) :=
    ⟨hnormF y hyN, hJX y.2⟩
  obtain ⟨n, hn⟩ := hN a haF ha1 (y : G) hyNF
  obtain ⟨a', ha', hne⟩ := hy n
  apply hne
  have hFa' : ((a' : ↥J) : G) ∈ F := (Subgroup.mem_subgroupOf.1 ha').1
  have hcomm'' := Subgroup.mem_centralizer_iff.1 hn ((a' : ↥J) : G) hFa'
  exact Subtype.ext (by simpa using hcomm''.symm)

end Aux

end CFSG.LocalAnalysis.RankThreeTheoremC
