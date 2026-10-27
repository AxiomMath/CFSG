module

public import CFSG.CGT.PushingUpLit.CGT6.OmegaPlusAdm
public import CFSG.CGT.PushingUpLit.CGT6.OmegaPlusNoAlt

public section

namespace CFSG.CGT.PushingUpLit.CGT6.OmegaPlus

open CFSG CFSG.Quasithin CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.CGT6
  CFSG.CGT.PushingUpLit.BHS6 CFSG.CGT.PushingUp

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem card_natSL {X : Subgroup (MulAut V)} {P : Subgroup V} {n : ℕ}
    (hnat : IsNatSectionBy (slAct n) X P ⊥) (hn : n ≠ 0) : Nat.card ↥P = 2 ^ (2 * n) := by
  obtain ⟨-, θ, β, hβs, hβk, -⟩ := hnat
  have hβi : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  rw [Nat.card_congr (Equiv.ofBijective β ⟨hβi, hβs⟩),
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 2 → Fq n) ≃ _), Nat.card_fun,
    GaloisField.card 2 n hn, Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul, mul_comm]

theorem lift_eq_of_natSL (hV : ∀ v : V, v ^ 2 = 1) {n : ℕ} (hn : 2 ≤ n)
    {G' D' X₁ : Subgroup (MulAut V)} (hnat : IsNatSectionBy (slAct n) D' (commV D') ⊥)
    (hlift : Lift4 G' D' X₁) : D' = X₁ := by
  obtain ⟨hDX, -, -, h4⟩ := hlift
  rcases h4 with ⟨-, harr⟩ | ⟨m, hm, -, hsplit⟩
  · exact arrowNat_eq_of_natSL hV hn hnat hDX harr
  · rcases hsplit with heq | ⟨-, ⟨e⟩, hcard⟩
    · exact heq
    · exfalso
      obtain ⟨-, θ, -⟩ := id hnat
      have hord : 2 ^ n * (2 ^ (2 * n) - 1) = 2 ^ m * (2 ^ (2 * m) - 1) := by
        rw [← card_sl2_fq (by omega : 1 ≤ n), ← card_sl2_fq (by omega : 1 ≤ m)]
        exact Nat.card_congr (θ.symm.trans e).toEquiv
      have hnm : n = m := sl2_order_inj (by omega) (by omega) hord
      subst hnm
      rw [card_natSL hnat (by omega)] at hcard
      have := Nat.pow_right_injective (le_refl 2) hcard
      omega

theorem star_root (hV : ∀ v : V, v ^ 2 = 1) {G T Y D B : Subgroup (MulAut V)} {n : ℕ}
    (cfg : Emb4Cfg G T Y) (hP : PlusSide G Y D B n) {b : MulAut V} (hb : b ∈ B)
    (hb2 : b ^ 2 = 1) (hb1 : b ≠ 1) :
    (D.subgroupOf (G ⊓ Subgroup.centralizer ({b} : Set (MulAut V)))).IsSubnormal := by
  obtain ⟨t, htT, ht1, ht2', -⟩ := exists_central_involution cfg.adm.hT1 cfg.adm.hT2
  have ht2 : t ^ 2 = 1 := by rw [pow_two]; exact ht2'
  have h := ginv_cent G b
  have hadm := adm4_bar hV cfg hP hb hb2 hb1 htT ht1 ht2
  have hsm : Smaller (resG (G ⊓ Subgroup.centralizer ({b} : Set (MulAut V)))
      (fixV (Subgroup.zpowers b)) h).range G := Or.inl (card_xbar_lt (hP.yg (hP.by_ hb)) hb1)
  obtain ⟨X₁, hlift⟩ := cfg.ih ↥(fixV (Subgroup.zpowers b))
    (fun v => Subtype.ext (by simpa using hV v)) _ hsm (isKGroup_xbar cfg.kgroup) _ _ hadm
  have heq := lift_eq_of_natSL (fun v => Subtype.ext (by simpa using hV v)) hP.hn
    (natSL_bar hP hb hb2 hb1) hlift
  have hs : ((barW h D).subgroupOf (resG (G ⊓ Subgroup.centralizer ({b} : Set (MulAut V)))
      (fixV (Subgroup.zpowers b)) h).range).IsSubnormal := heq ▸ hlift.2.2.1
  refine subnormal_of_bar h (fun k hk hkf d hd => ?_) hs
  have hkb : k * b = b * k := (Subgroup.mem_centralizer_iff.mp hk.2 b rfl).symm
  have hkK : k ∈ kStab G b := mem_kStab.mpr ⟨⟨hk.1, hkb⟩, fun v hv => hkf v hv⟩
  exact kStab_comm_D hV cfg hP hb hb2 k hkK d hd

end CFSG.CGT.PushingUpLit.CGT6.OmegaPlus
