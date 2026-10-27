module

public import Certificates.Certificate21202

public section

namespace CFSG.LargeExtraspecial.AS62

open CFSG.CosetTable


theorem relsB_finite_and_card_le :
    Finite (PG 4 relsB) ∧ Nat.card (PG 4 relsB) ≤ 192 :=
  Certificates.certificate21202.1

theorem rels1_finite_and_card_le :
    Finite (PG 5 rels1) ∧ Nat.card (PG 5 rels1) ≤ 576 :=
  Certificates.certificate21202.2.1

theorem rels2_finite_and_card_le :
    Finite (PG 5 rels2) ∧ Nat.card (PG 5 rels2) ≤ 960 :=
  Certificates.certificate21202.2.2

instance finite_pg_relsB : Finite (PG 4 relsB) :=
  relsB_finite_and_card_le.1

instance finite_pg_rels1 : Finite (PG 5 rels1) :=
  rels1_finite_and_card_le.1

instance finite_pg_rels2 : Finite (PG 5 rels2) :=
  rels2_finite_and_card_le.1

theorem relsB_card_le : Nat.card (PG 4 relsB) ≤ 192 :=
  relsB_finite_and_card_le.2

theorem rels1_card_le : Nat.card (PG 5 rels1) ≤ 576 :=
  rels1_finite_and_card_le.2

theorem rels2_card_le : Nat.card (PG 5 rels2) ≤ 960 :=
  rels2_finite_and_card_le.2

end CFSG.LargeExtraspecial.AS62
